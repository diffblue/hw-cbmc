/*******************************************************************\

Module: FastPPA Estimator

Author: Kiro

\*******************************************************************/

#include "fastppa_estimator.h"

#include <util/cmdline.h>
#include <util/exit_codes.h>
#include <util/format_expr.h>
#include <util/message.h>

#include <trans-netlist/netlist.h>
#include <trans-netlist/trans_to_netlist.h>

#include "estimate.h"
#include "fastppa_error.h"
#include "fastppa_frontend.h"
#include "technology_db.h"

#include <cmath>
#include <iomanip>
#include <iostream>
#include <set>
#include <sstream>

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

  const namespacet ns(model.transition_system.symbol_table);
  messaget message(message_handler);
  estimation_resultt result;

  if(cmdline.isset("netlist"))
  {
    // Netlist path: convert to AIG, count AND gates
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
    std::size_t latches = netlist.var_map.latches.size();

    for(std::size_t i = 0; i < netlist.nodes.size(); i++)
    {
      auto &node = netlist.nodes[i];
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

    result.register_bits = latches;
    result.register_area_um2 =
      static_cast<double>(latches) * tech.register_cost(1).area_um2;
    result.operator_count = and_gates;
    result.combinational_area_um2 = static_cast<double>(and_gates) *
                                    tech.operator_cost(ID_bitand, 1).area_um2;
    result.total_area_um2 =
      result.register_area_um2 + result.combinational_area_um2;
    result.combinational_depth = 0;
    result.critical_path_ps = 0;

    message.status() << "Netlist: " << and_gates << " unique AND gates, "
                     << latches << " latches" << messaget::eom;
  }
  else
  {
    // Word-level path
    for(const auto &[id, expr] : model.wl_trans->next_state_functions)
    {
      message.debug() << "NSF " << id << "' = " << format(expr)
                      << messaget::eom;
    }

    result = estimate(
      *model.wl_trans,
      model.transition_system.trans_expr,
      model.state_vars,
      tech,
      ns);
  }

  // Power parameters
  double clock_freq = 1e9;
  if(cmdline.isset("clock-freq"))
  {
    try
    {
      clock_freq = std::stod(cmdline.get_value("clock-freq"));
    }
    catch(...)
    {
      throw fastppa_errort{} << "invalid --clock-freq value: "
                             << cmdline.get_value("clock-freq");
    }
  }

  double toggle_rate = 0.1;
  if(cmdline.isset("toggle-rate"))
  {
    try
    {
      toggle_rate = std::stod(cmdline.get_value("toggle-rate"));
    }
    catch(...)
    {
      throw fastppa_errort{} << "invalid --toggle-rate value: "
                             << cmdline.get_value("toggle-rate");
    }
  }

  double effective_toggle = toggle_rate * result.activity_ratio;
  double dynamic_power_mw =
    result.total_energy_fj * clock_freq * effective_toggle / 1e9;

  // Leakage power: proportional to area and process-dependent
  // ~0.1 mW per 1000 µm² at 45nm baseline
  double leakage_power_mw =
    result.total_area_um2 * 0.0001 * tech.leakage_scale();

  // Clock tree power: ~30-35% of dynamic for advanced nodes
  double clock_tree_fraction = tech.wire_delay_fraction() > 0.3 ? 0.35 : 0.25;
  double clock_tree_power_mw = dynamic_power_mw * clock_tree_fraction;

  double total_power_mw =
    dynamic_power_mw + leakage_power_mw + clock_tree_power_mw;

  // Timing: setup + wire delay
  double setup_ps = tech.register_cost(1).delay_ps;
  double wire_delay_ps = 0;
  if(result.combinational_area_um2 > 0 && result.combinational_depth > 0)
  {
    double avg_dimension_um = std::sqrt(result.total_area_um2);
    double wire_ps_per_um = 0.1 * tech.register_cost(1).delay_ps / 50.0;
    double avg_fanout = result.operator_count > 0
                          ? static_cast<double>(result.operator_count) /
                              result.combinational_depth
                          : 1.0;
    wire_delay_ps = result.combinational_depth * avg_dimension_um *
                    wire_ps_per_um * std::sqrt(avg_fanout) * 0.1;
    double max_wire = result.critical_path_ps * tech.wire_delay_fraction();
    if(wire_delay_ps > max_wire)
      wire_delay_ps = max_wire;
  }
  double reg_to_reg_ps = result.critical_path_ps + wire_delay_ps + setup_ps;

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
  out << "  Setup time:          " << setup_ps << " ps\n";
  out << "  Wire delay:          " << wire_delay_ps << " ps\n";
  out << "  Reg-to-reg delay:    " << reg_to_reg_ps << " ps";
  out << " (" << std::setprecision(3) << reg_to_reg_ps / 1000.0 << " ns)\n";
  double period_ps = 1e12 / clock_freq;
  double slack = period_ps - reg_to_reg_ps;
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
  out << "  Dynamic:             " << std::setprecision(3) << dynamic_power_mw
      << " mW\n";
  out << "  Clock tree:          " << clock_tree_power_mw << " mW\n";
  out << "  Leakage:             " << leakage_power_mw << " mW\n";
  out << "  Total:               " << total_power_mw << " mW\n";
  out << "\n";

  message.status() << out.str() << messaget::eom;

  return 0;
}
