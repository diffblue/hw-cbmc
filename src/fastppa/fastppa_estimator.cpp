/*******************************************************************\

Module: FastPPA Estimator

Author: Kiro

\*******************************************************************/

#include "fastppa_estimator.h"

#include <util/cmdline.h>
#include <util/exit_codes.h>
#include <util/message.h>
#include <util/namespace.h>

#include <ebmc/ebmc_error.h>
#include <trans-netlist/netlist.h>
#include <trans-netlist/trans_to_netlist.h>

#include "cost_table.h"
#include "estimate.h"
#include "fastppa_frontend.h"
#include "technology_db.h"

#include <cmath>
#include <iomanip>
#include <iostream>
#include <set>
#include <sstream>

// Leakage power: ~0.1 mW per 1000 µm² at the 45nm baseline.
static constexpr double LEAKAGE_MW_PER_UM2 = 0.0001;

// Clock tree power as a fraction of dynamic power: ~30-35% for advanced
// nodes (which have a high wire-delay fraction), ~25% otherwise.
static constexpr double CLOCK_TREE_FRACTION_ADVANCED = 0.35;
static constexpr double CLOCK_TREE_FRACTION_MATURE = 0.25;

/// Parse a floating-point command-line option, rejecting values with
/// trailing garbage (std::stod would silently accept, e.g., "1GHz" as 1).
static double parse_double_option(const cmdlinet &cmdline, const char *option)
{
  const auto value = cmdline.get_value(option);
  std::size_t consumed = 0;
  double result = 0;

  try
  {
    result = std::stod(value, &consumed);
  }
  catch(...)
  {
    consumed = 0;
  }

  if(consumed != value.size() || value.empty())
    throw ebmc_errort{}.with_exit_code(CPROVER_EXIT_USAGE_ERROR)
      << "invalid --" << option << " value: " << value;

  return result;
}

/// Estimate by converting to an AIG netlist and counting its structure:
/// registers from the latch count, combinational area from the number of
/// structurally-distinct AND gates. No timing information.
static estimation_resultt estimate_from_netlist(
  fastppa_modelt &model,
  const technology_dbt &tech,
  message_handlert &message_handler)
{
  netlistt netlist;
  std::map<irep_idt, exprt> no_properties;
  convert_trans_to_netlist(
    model.transition_system.symbol_table,
    model.transition_system.main_symbol->name,
    model.transition_system.trans_expr,
    no_properties,
    netlist,
    message_handler);

  // Structural hashing: deduplicate AND gates
  std::set<std::pair<unsigned, unsigned>> unique_ands;

  for(const auto &node : netlist.nodes)
  {
    if(!node.is_and())
      continue;
    if(node.a.is_constant() || node.b.is_constant())
      continue;
    if(node.a.var_no() == node.b.var_no())
      continue;

    unsigned key_a = node.a.var_no() * 2 + (node.a.sign() ? 1 : 0);
    unsigned key_b = node.b.var_no() * 2 + (node.b.sign() ? 1 : 0);
    if(key_a > key_b)
      std::swap(key_a, key_b);
    unique_ands.insert({key_a, key_b});
  }

  std::size_t and_gates = unique_ands.size();
  std::size_t latches = netlist.var_map.latches.size();

  estimation_resultt result;
  result.register_bits = latches;
  result.register_area_um2 =
    static_cast<double>(latches) * tech.register_cost(1).area_um2;
  result.operator_count = and_gates;
  result.combinational_area_um2 =
    static_cast<double>(and_gates) * tech.operator_cost(ID_bitand, 1).area_um2;
  result.total_area_um2 =
    result.register_area_um2 + result.combinational_area_um2;
  result.combinational_depth = 0;
  result.critical_path_ps = 0;

  messaget message(message_handler);
  message.status() << "Netlist: " << and_gates << " unique AND gates, "
                   << latches << " latches" << messaget::eom;

  return result;
}

struct power_estimatet
{
  double dynamic_mw = 0;
  double clock_tree_mw = 0;
  double leakage_mw = 0;

  double total_mw() const
  {
    return dynamic_mw + clock_tree_mw + leakage_mw;
  }
};

static power_estimatet power_estimate(
  const estimation_resultt &result,
  const technology_dbt &tech,
  double clock_freq,
  double effective_toggle)
{
  power_estimatet power;
  power.dynamic_mw =
    result.total_energy_fj * clock_freq * effective_toggle / 1e9;
  power.leakage_mw =
    result.total_area_um2 * LEAKAGE_MW_PER_UM2 * tech.leakage_scale();
  double clock_tree_fraction = tech.wire_delay_fraction() > 0.3
                                 ? CLOCK_TREE_FRACTION_ADVANCED
                                 : CLOCK_TREE_FRACTION_MATURE;
  power.clock_tree_mw = power.dynamic_mw * clock_tree_fraction;
  return power;
}

int run_fastppa_estimation(
  const cmdlinet &cmdline,
  message_handlert &message_handler)
{
  // Determine process node
  std::string process = "45nm";
  if(cmdline.isset("process"))
    process = cmdline.get_value("process");

  technology_dbt tech(process);

  // Build model from Verilog
  auto model = build_fastppa_model(cmdline, message_handler);

  messaget message(message_handler);
  estimation_resultt result;

  if(cmdline.isset("netlist"))
  {
    result = estimate_from_netlist(model, tech, message_handler);
  }
  else
  {
    const auto table =
      cmdline.isset("cost-table")
        ? cost_tablet::from_file(cmdline.get_value("cost-table"))
        : cost_tablet::builtin("nangate45");
    const namespacet ns{model.transition_system.symbol_table};
    result = estimate(
      model.transition_system.trans_expr,
      model.state_vars,
      model.outputs,
      ns,
      table,
      tech,
      message_handler);
  }

  // Power parameters
  double clock_freq = 1e9;
  if(cmdline.isset("clock-freq"))
  {
    clock_freq = parse_double_option(cmdline, "clock-freq");
    // !(x > 0) also rejects NaN
    if(!(clock_freq > 0))
      throw ebmc_errort{}.with_exit_code(CPROVER_EXIT_USAGE_ERROR)
        << "--clock-freq must be positive";
  }

  double toggle_rate = 0.1;
  if(cmdline.isset("toggle-rate"))
  {
    toggle_rate = parse_double_option(cmdline, "toggle-rate");
    if(!(toggle_rate >= 0 && toggle_rate <= 1))
      throw ebmc_errort{}.with_exit_code(CPROVER_EXIT_USAGE_ERROR)
        << "--toggle-rate must be between 0 and 1";
  }

  double effective_toggle = toggle_rate;
  auto power = power_estimate(result, tech, clock_freq, effective_toggle);

  // Output results
  std::ostringstream out;
  out << std::fixed << std::setprecision(1);

  out << "\n";
  out << "RTL Cost Estimation (" << process << ")\n";
  out << std::string(40, '=') << "\n\n";

  out << "Registers:\n";
  out << "  State variables:     " << model.state_vars.size() << "\n";
  out << "  Register bits:       " << result.register_bits << "\n";
  out << "  Register area:       " << result.register_area_um2 << " um2\n";
  out << "\n";

  out << "Combinational logic:\n";
  out << "  Operators:           " << result.operator_count << "\n";
  out << "  Comb. depth:         " << result.combinational_depth << " levels\n";
  out << "  Comb. area:          " << result.combinational_area_um2 << " um2\n";
  out << "\n";

  out << "Timing:\n";
  out << "  Critical path:       " << result.critical_path_ps << " ps";
  out << " (" << std::setprecision(3) << result.critical_path_ps / 1000.0
      << " ns)\n";
  out << std::setprecision(1);
  double period_ps = 1e12 / clock_freq;
  double slack = period_ps - result.critical_path_ps;
  out << std::setprecision(1);
  out << "  Clock period:        " << period_ps << " ps";
  out << " (" << clock_freq / 1e6 << " MHz)\n";
  out << "  Slack:               " << slack << " ps";
  if(slack < 0)
    out << " [TIMING VIOLATION]";
  out << "\n\n";

  out << "Area:\n";
  out << "  Total:               " << result.total_area_um2 << " um2\n";
  out << "\n";

  out << "Power (estimated, alpha=" << std::setprecision(2) << effective_toggle
      << "):\n";
  out << "  Dynamic:             " << std::setprecision(3) << power.dynamic_mw
      << " mW\n";
  out << "  Clock tree:          " << power.clock_tree_mw << " mW\n";
  out << "  Leakage:             " << power.leakage_mw << " mW\n";
  out << "  Total:               " << power.total_mw() << " mW\n";
  out << "\n";

  message.status() << out.str() << messaget::eom;

  return 0;
}
