/*******************************************************************\

Module: FastPPA Estimator

Author: Kiro

\*******************************************************************/

#include "fastppa_estimator.h"

#include <util/cmdline.h>
#include <util/exit_codes.h>
#include <util/expr_iterator.h>
#include <util/json.h>
#include <util/message.h>
#include <util/namespace.h>

#include <ebmc/ebmc_error.h>
#include <trans-netlist/netlist.h>
#include <trans-netlist/trans_to_netlist.h>

#include "cost_table.h"
#include "estimate.h"
#include "fastppa_frontend.h"

#include <algorithm>
#include <cmath>
#include <iomanip>
#include <iostream>
#include <sstream>

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

/// Estimate by converting to an AIG netlist. Area, energy and leakage
/// count the AND gates and latches that reach an output, directly or
/// through latches; the delay is the longest path in AND gates. The cost
/// of an AND gate ('aig_and') and its delay per level are fitted on the
/// calibration designs (benchmarking/fastppa_eval/fit.py).
static estimation_resultt estimate_from_netlist(
  fastppa_modelt &model,
  const cost_tablet &table,
  message_handlert &message_handler)
{
  // Put the operands of commutative operators into a canonical order, so
  // that a*b and b*a become the same gates. Equalities are left alone:
  // the definitions of wires and next states are equalities.
  transt trans = model.transition_system.trans_expr;
  for(auto it = trans.depth_begin(); it != trans.depth_end(); ++it)
  {
    const auto &id = it->id();
    if(
      id == ID_plus || id == ID_mult || id == ID_bitand || id == ID_bitor ||
      id == ID_bitxor || id == ID_and || id == ID_or)
    {
      if(std::is_sorted(it->operands().begin(), it->operands().end()))
        continue;
      auto &operands = it.mutate().operands();
      std::sort(operands.begin(), operands.end());
    }
  }

  netlistt netlist;
  std::map<irep_idt, exprt> no_properties;
  convert_trans_to_netlist(
    model.transition_system.symbol_table,
    model.transition_system.main_symbol->name,
    trans,
    no_properties,
    netlist,
    message_handler);

  const std::size_t n_nodes = netlist.nodes.size();

  // latch variable -> next-state literal
  std::map<std::size_t, literalt> latch_next;
  for(const auto &[id, var] : netlist.var_map.map)
    if(var.is_latch())
      for(const auto &bit : var.bits)
        latch_next[bit.current.var_no()] = bit.next;

  // the bits of the top-level output ports, which may be latches
  std::vector<literalt> outputs;
  for(const auto &output : model.outputs)
  {
    auto it = netlist.var_map.map.find(output.get_identifier());
    if(it == netlist.var_map.map.end())
      throw ebmc_errort{} << "output " << output.get_identifier()
                          << " is not in the netlist";
    for(const auto &bit : it->second.bits)
      outputs.push_back(bit.current);
  }

  // Cone of influence of the outputs. The bit-blaster encodes some
  // operators (e.g., division, and array accesses) relationally: their
  // results are fresh variables, constrained by netlist.constraints and
  // netlist.equivalences. When such a variable is reached, the
  // constraints are part of the cone. This counts the gates of the
  // checking circuit, not those of the operator.
  std::vector<bool> is_nondet(n_nodes, false);
  for(const auto &[id, var] : netlist.var_map.map)
    if(var.is_nondet())
      for(const auto &bit : var.bits)
        if(bit.current.var_no() < n_nodes)
          is_nondet[bit.current.var_no()] = true;

  std::vector<bool> live(n_nodes, false);
  std::vector<std::size_t> stack;
  auto push = [&](literalt l)
  {
    if(!l.is_constant() && l.var_no() < n_nodes && !live[l.var_no()])
      stack.push_back(l.var_no());
  };
  for(auto l : outputs)
    push(l);
  bool constraints_added = false;
  while(!stack.empty())
  {
    auto v = stack.back();
    stack.pop_back();
    if(live[v])
      continue;
    live[v] = true;
    const auto &node = netlist.nodes[v];
    if(node.is_and())
    {
      push(node.a);
      push(node.b);
    }
    else if(auto it = latch_next.find(v); it != latch_next.end())
      push(it->second);
    else if(is_nondet[v] && !constraints_added)
    {
      constraints_added = true;
      for(auto l : netlist.constraints)
        push(l);
      for(auto &[a, b] : netlist.equivalences)
      {
        push(a);
        push(b);
      }
    }
  }

  std::size_t and_gates = 0, latches = 0;
  for(std::size_t v = 0; v < n_nodes; ++v)
  {
    if(!live[v])
      continue;
    if(netlist.nodes[v].is_and())
      ++and_gates;
    else if(latch_next.count(v) != 0)
      ++latches;
  }

  std::vector<literalt> endpoints = outputs;
  for(auto &[v, next] : latch_next)
    if(live[v])
      endpoints.push_back(next);

  // Longest paths, in a given delay per AND gate, starting at a given
  // time at the latches. The nodes are in dependency order, except that
  // a relationally encoded result (a nondet variable) only becomes
  // available when its constraints do; this needs a second pass.
  auto longest = [&](double and_delay, double latch_start)
  {
    std::vector<double> t(n_nodes, 0);
    auto t_of = [&](literalt l)
    { return l.is_constant() ? 0.0 : t[l.var_no()]; };
    double nondet_start = 0;
    for(int pass = 0; pass < 2; ++pass)
    {
      for(std::size_t v = 0; v < n_nodes; ++v)
      {
        if(!live[v])
          continue;
        const auto &node = netlist.nodes[v];
        if(node.is_and())
          t[v] = std::max(t_of(node.a), t_of(node.b)) + and_delay;
        else if(latch_next.count(v) != 0)
          t[v] = latch_start;
        else if(is_nondet[v])
          t[v] = nondet_start;
      }
      if(!constraints_added)
        break;
      for(auto l : netlist.constraints)
        nondet_start = std::max(nondet_start, t_of(l));
    }
    double worst = 0;
    for(auto l : endpoints)
      worst = std::max(worst, t_of(l));
    return worst;
  };

  const auto levels = static_cast<std::size_t>(longest(1, 0));

  {
    std::size_t all_ands = 0;
    for(const auto &node : netlist.nodes)
      if(node.is_and())
        ++all_ands;
    messaget{message_handler}.statistics()
      << "Netlist before cone of influence: " << all_ands << " AND gates, "
      << latch_next.size() << " latches; " << outputs.size() << " output bits"
      << messaget::eom;
  }

  // Printed before the costs are looked up, so that fit.py can use it
  // with a table that has no 'aig_and' entry yet.
  messaget message(message_handler);
  message.status() << "Netlist: " << and_gates << " AND gates, " << latches
                   << " latches, " << levels << " levels" << messaget::eom;

  const auto &aig_and = table("aig_and");
  const auto &reg = table("register");

  estimation_resultt result;
  result.critical_path_ps = longest(aig_and.delay(1), reg.delay(1));

  result.register_bits = latches;
  result.register_area_um2 = latches * reg.area(1);
  result.operator_count = and_gates;
  result.combinational_area_um2 = and_gates * aig_and.area(1);
  result.total_area_um2 =
    result.register_area_um2 + result.combinational_area_um2;
  result.combinational_depth = levels;
  result.data_energy_fj =
    and_gates * aig_and.energy(1) + latches * reg.energy(1);
  result.clock_energy_fj = latches * table("clock").energy(1);
  result.leakage_uw = and_gates * aig_and.leakage(1) + latches * reg.leakage(1);

  return result;
}

/// Symbol names without the language prefix and the $root module.
static std::string display_name(const irep_idt &identifier)
{
  std::string s = id2string(identifier);
  for(const std::string prefix : {"Verilog::", "$root."})
    if(s.rfind(prefix, 0) == 0)
      s = s.substr(prefix.size());
  return s;
}

static json_numbert number(double value)
{
  std::ostringstream s;
  s << value;
  return json_numbert{s.str()};
}

static std::size_t
parse_unsigned_option(const cmdlinet &cmdline, const char *option)
{
  const auto value = cmdline.get_value(option);
  if(
    value.empty() || value.find_first_not_of("0123456789") != std::string::npos)
    throw ebmc_errort{}.with_exit_code(CPROVER_EXIT_USAGE_ERROR)
      << "invalid --" << option << " value: " << value;
  return std::stoul(value);
}

struct power_estimatet
{
  double dynamic_mw = 0;
  double clock_mw = 0;
  double leakage_mw = 0;

  double total_mw() const
  {
    return dynamic_mw + clock_mw + leakage_mw;
  }
};

/// Dynamic power is the switching energy per cycle at the given toggle
/// rate; clock power is the energy of the registers' clock pins, which
/// toggle every cycle whatever the data do. There is no clock tree.
static power_estimatet power_estimate(
  const estimation_resultt &result,
  double clock_freq,
  double toggle_rate)
{
  // fJ * Hz = 1e-15 W = 1e-12 mW
  power_estimatet power;
  power.dynamic_mw = result.data_energy_fj * toggle_rate * clock_freq * 1e-12;
  power.clock_mw = result.clock_energy_fj * clock_freq * 1e-12;
  power.leakage_mw = result.leakage_uw * 1e-3;
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

  const auto table = cmdline.isset("cost-table")
                       ? cost_tablet::from_file(cmdline.get_value("cost-table"))
                       : cost_tablet::builtin(process);

  // Build model from Verilog
  auto model = build_fastppa_model(cmdline, message_handler);

  messaget message(message_handler);
  estimation_resultt result;

  if(cmdline.isset("netlist"))
  {
    result = estimate_from_netlist(model, table, message_handler);
  }
  else
  {
    const namespacet ns{model.transition_system.symbol_table};
    result = estimate(
      model.transition_system.trans_expr,
      model.state_vars,
      model.outputs,
      ns,
      table,
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

  auto power = power_estimate(result, clock_freq, toggle_rate);

  std::size_t number_of_paths = 3;
  if(cmdline.isset("paths"))
    number_of_paths = parse_unsigned_option(cmdline, "paths");

  if(cmdline.isset("json"))
  {
    json_objectt json;
    json["process"] = json_stringt{process};
    json["register_bits"] = json_numbert{std::to_string(result.register_bits)};
    json["area_um2"] = json_objectt{
      {"total", number(result.total_area_um2)},
      {"registers", number(result.register_area_um2)},
      {"combinational", number(result.combinational_area_um2)}};
    json["critical_path_ps"] = number(result.critical_path_ps);
    json["clock_frequency_hz"] = number(clock_freq);
    json["toggle_rate"] = number(toggle_rate);
    json["power_mw"] = json_objectt{
      {"dynamic", number(power.dynamic_mw)},
      {"clock", number(power.clock_mw)},
      {"leakage", number(power.leakage_mw)},
      {"total", number(power.total_mw())}};
    json_arrayt paths;
    for(std::size_t i = 0;
        i < number_of_paths && i < result.critical_paths.size();
        ++i)
    {
      const auto &path = result.critical_paths[i];
      json_arrayt steps;
      for(auto &step : path.steps)
      {
        json_objectt j{
          {"operation", json_stringt{step.operation}},
          {"name", json_stringt{display_name(step.name)}},
          {"width", json_numbert{std::to_string(step.width)}},
          {"arrival_ps", number(step.arrival_ps)}};
        if(!step.source_location.get_file().empty())
        {
          j["file"] = json_stringt{step.source_location.get_file()};
          j["line"] = json_stringt{step.source_location.get_line()};
        }
        steps.push_back(std::move(j));
      }
      paths.push_back(json_objectt{
        {"endpoint", json_stringt{display_name(path.endpoint)}},
        {"endpoint_kind",
         json_stringt{path.endpoint_is_register ? "register" : "output"}},
        {"arrival_ps", number(path.arrival_ps)},
        {"steps", std::move(steps)}});
    }
    json["critical_paths"] = std::move(paths);
    std::cout << json << '\n';
    return 0;
  }

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

  if(number_of_paths != 0 && !result.critical_paths.empty())
  {
    out << "Critical paths:\n";
    for(std::size_t i = 0;
        i < number_of_paths && i < result.critical_paths.size();
        ++i)
    {
      const auto &path = result.critical_paths[i];
      out << "  " << i + 1 << ". " << path.arrival_ps << " ps to "
          << (path.endpoint_is_register ? "register " : "output ")
          << display_name(path.endpoint) << "\n";
      for(auto &step : path.steps)
      {
        std::ostringstream what;
        what << step.operation;
        if(!step.name.empty())
          what << ' ' << display_name(step.name);
        if(step.width != 0)
          what << " (" << step.width << " bits)";
        out << "       " << std::left << std::setw(32) << what.str()
            << std::right << std::setw(9) << step.arrival_ps << " ps";
        if(!step.source_location.get_line().empty())
          out << "  " << step.source_location.get_file() << ':'
              << step.source_location.get_line();
        out << "\n";
      }
    }
    out << "\n";
  }

  out << "Area:\n";
  out << "  Total:               " << result.total_area_um2 << " um2\n";
  out << "\n";

  out << "Power (estimated, alpha=" << std::setprecision(2) << toggle_rate
      << "):\n";
  out << "  Dynamic:             " << std::setprecision(6) << power.dynamic_mw
      << " mW\n";
  out << "  Clock:               " << power.clock_mw << " mW\n";
  out << "  Leakage:             " << power.leakage_mw << " mW\n";
  out << "  Total:               " << power.total_mw() << " mW\n";
  out << "\n";

  message.status() << out.str() << messaget::eom;

  return 0;
}
