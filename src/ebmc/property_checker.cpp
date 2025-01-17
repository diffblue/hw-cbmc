/*******************************************************************\

Module: EBMC Property Checker

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "property_checker.h"

#include <util/string2int.h>

#include <solvers/sat/satcheck.h>
#include <trans-netlist/trans_trace_netlist.h>
#include <trans-netlist/unwind_netlist.h>

#include "bdd_engine.h"
#include "bmc.h"
#include "dimacs_writer.h"
#include "ebmc_error.h"
#include "ebmc_solver_factory.h"
#include "ic3_engine.h"
#include "k_induction.h"
#include "netlist.h"
#include "output_file.h"
#include "report_results.h"

#include <chrono>
#include <iostream>

property_checker_resultt word_level_bmc(
  const cmdlinet &cmdline,
  const transition_systemt &transition_system,
  const ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  auto solver_factory = ebmc_solver_factory(cmdline);

  bool convert_only = cmdline.isset("smt2") || cmdline.isset("outfile") ||
                      cmdline.isset("show-formula");

  try
  {
    if(cmdline.isset("max-bound"))
    {
      if(convert_only)
        throw ebmc_errort() << "please set a specific bound";

      const std::size_t max_bound =
        unsafe_string2size_t(cmdline.get_value("max-bound"));

      for(std::size_t bound = 1; bound <= max_bound; bound++)
      {
        messaget message{message_handler};
        message.status() << "Doing BMC with bound " << bound << messaget::eom;

#if 0
        const namespacet ns(transition_system.symbol_table);
        CHECK_RETURN(trans_expr.has_value());
        ::unwind(*trans_expr, *message_handler, solver, bound+1, ns, true);
        result=finish_word_level_bmc(solver);
#endif
      }

      return property_checker_resultt{properties};
    }
    else
    {
      std::size_t bound;

      if(cmdline.isset("bound"))
      {
        bound = unsafe_string2unsigned(cmdline.get_value("bound"));
      }
      else
      {
        messaget message{message_handler};
        message.warning() << "using default bound 1" << messaget::eom;
        bound = 1;
      }

      if(!convert_only)
        if(properties.properties.empty())
          throw "no properties";

      bool bmc_with_assumptions = cmdline.isset("bmc-with-assumptions");

      auto result = bmc(
        bound,
        convert_only,
        bmc_with_assumptions,
        transition_system,
        properties,
        solver_factory,
        message_handler);

      if(convert_only)
        return property_checker_resultt::success();

      return result;
    }
  }

  catch(const char *e)
  {
    messaget message{message_handler};
    message.error() << e << messaget::eom;
    return property_checker_resultt::error();
  }

  catch(const std::string &e)
  {
    messaget message{message_handler};
    message.error() << e << messaget::eom;
    return property_checker_resultt::error();
  }

  catch(int)
  {
    return property_checker_resultt::error();
  }
}

property_checker_resultt finish_bit_level_bmc(
  std::size_t bound,
  const bmc_mapt &bmc_map,
  propt &solver,
  const transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  auto sat_start_time = std::chrono::steady_clock::now();

  messaget message{message_handler};
  message.status() << "Solving with " << solver.solver_text() << messaget::eom;

  for(auto &property : properties.properties)
  {
    if(property.is_disabled())
      continue;

    if(property.is_failure())
      continue;

    if(property.is_assumed())
      continue;

    message.status() << "Checking " << property.name << messaget::eom;

    literalt property_literal = !solver.land(property.timeframe_literals);

    bvt assumptions;
    assumptions.push_back(property_literal);

    propt::resultt prop_result = solver.prop_solve(assumptions);

    switch(prop_result)
    {
    case propt::resultt::P_SATISFIABLE:
    {
      property.refuted();
      message.result() << "SAT: counterexample found" << messaget::eom;

      namespacet ns{transition_system.symbol_table};

      property.witness_trace =
        compute_trans_trace(property.timeframe_literals, bmc_map, solver, ns);
    }
    break;

    case propt::resultt::P_UNSATISFIABLE:
      message.result() << "UNSAT: No counterexample found within bound"
                       << messaget::eom;
      property.proved_with_bound(bound);
      break;

    case propt::resultt::P_ERROR:
      message.error() << "Error from decision procedure" << messaget::eom;
      return property_checker_resultt::error();

    default:
      message.error() << "Unexpected result from decision procedure"
                      << messaget::eom;
      return property_checker_resultt::error();
    }
  }

  auto sat_stop_time = std::chrono::steady_clock::now();

  message.statistics()
    << "Solver time: "
    << std::chrono::duration<double>(sat_stop_time - sat_start_time).count()
    << messaget::eom;

  return property_checker_resultt{properties};
}

property_checker_resultt bit_level_bmc(
  cnft &solver,
  bool convert_only,
  const cmdlinet &cmdline,
  transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  messaget message{message_handler};

  std::size_t bound;

  if(cmdline.isset("bound"))
  {
    bound = unsafe_string2unsigned(cmdline.get_value("bound"));
  }
  else
  {
    message.warning() << "using default bound 1" << messaget::eom;
    bound = 1;
  }

  try
  {
    if(!convert_only)
      if(properties.properties.empty())
        throw "no properties";

    // make net-list
    message.status() << "Generating Netlist" << messaget::eom;

    auto netlist = make_netlist(transition_system, properties, message_handler);

    message.statistics() << "Latches: " << netlist.var_map.latches.size()
                         << ", nodes: " << netlist.number_of_nodes()
                         << messaget::eom;

    messaget message{message_handler};
    message.status() << "Unwinding Netlist" << messaget::eom;

    const auto bmc_map = bmc_mapt{netlist, bound + 1, solver};

    ::unwind(netlist, bmc_map, message, solver);

    const namespacet ns(transition_system.symbol_table);

    // convert the properties
    for(auto &property : properties.properties)
    {
      if(property.is_disabled())
        continue;

      if(!netlist_bmc_supports_property(property.normalized_expr))
      {
        property.failure("property not supported by netlist BMC engine");
        continue;
      }

      // look up the property in the netlist
      auto netlist_property = netlist.properties.find(property.identifier);
      CHECK_RETURN(netlist_property != netlist.properties.end());

      property.timeframe_literals =
        ::unwind_property(netlist_property->second, bmc_map);

      if(property.is_assumed())
      {
        // force these to be true
        for(auto l : property.timeframe_literals)
          solver.l_set_to(l, true);
      }
      else
      {
        // freeze for incremental usage
        for(auto l : property.timeframe_literals)
          solver.set_frozen(l);
      }
    }

    if(convert_only)
      return property_checker_resultt::success();
    else
    {
      return finish_bit_level_bmc(
        bound, bmc_map, solver, transition_system, properties, message_handler);
    }
  }

  catch(const char *e)
  {
    messaget message{message_handler};
    message.error() << e << messaget::eom;
    return property_checker_resultt::error();
  }

  catch(const std::string &e)
  {
    messaget message{message_handler};
    message.error() << e << messaget::eom;
    return property_checker_resultt::error();
  }

  catch(int)
  {
    return property_checker_resultt::error();
  }
}

property_checker_resultt bit_level_bmc(
  const cmdlinet &cmdline,
  transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  if(cmdline.isset("dimacs"))
  {
    if(cmdline.isset("outfile"))
    {
      auto outfile = output_filet{cmdline.get_value("outfile")};

      messaget message{message_handler};
      message.status() << "Writing DIMACS CNF to `" << outfile.name() << "'"
                       << messaget::eom;

      dimacs_cnf_writert dimacs_cnf_writer{outfile.stream(), message_handler};

      return bit_level_bmc(
        dimacs_cnf_writer,
        true,
        cmdline,
        transition_system,
        properties,
        message_handler);
    }
    else
    {
      dimacs_cnf_writert dimacs_cnf_writer{std::cout, message_handler};

      return bit_level_bmc(
        dimacs_cnf_writer,
        true,
        cmdline,
        transition_system,
        properties,
        message_handler);
    }
  }
  else
  {
    if(cmdline.isset("outfile"))
      throw ebmc_errort()
        << "Cannot write to outfile without file format option";

    satcheckt satcheck{message_handler};

    messaget message{message_handler};
    message.status() << "Using " << satcheck.solver_text() << messaget::eom;

    return bit_level_bmc(
      satcheck, false, cmdline, transition_system, properties, message_handler);
  }
}

property_checker_resultt engine_heuristic(
  const cmdlinet &cmdline,
  transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  if(properties.properties.empty())
  {
    message.error() << "no properties" << messaget::eom;
    return property_checker_resultt::error();
  }

  auto solver_factory = ebmc_solver_factory(cmdline);

  if(!properties.has_unfinished_property())
    return property_checker_resultt{properties}; // done

  message.status() << "No engine given, attempting heuristic engine selection"
                   << messaget::eom;

  // First try 1-induction, word-level
  message.status() << "Attempting 1-induction" << messaget::eom;

  k_induction(
    1, transition_system, properties, solver_factory, message_handler);

  if(!properties.has_unfinished_property())
    return property_checker_resultt{properties}; // done

  properties.reset_failure();
  properties.reset_inconclusive();
  properties.reset_unsupported();

  // Now try BMC with bound 5, word-level
  message.status() << "Attempting BMC with bound 5" << messaget::eom;

  auto bmc_result = bmc(
    5,     // bound
    false, // convert_only
    cmdline.isset("bmc-with-assumptions"),
    transition_system,
    properties,
    solver_factory,
    message_handler);

  properties.properties = std::move(bmc_result.properties);

  if(!properties.has_unfinished_property())
    return property_checker_resultt{properties}; // done

  properties.reset_failure();

  // Give up
  return property_checker_resultt{properties}; // done
}

property_checker_resultt property_checker(
  const cmdlinet &cmdline,
  transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  auto result = [&]() -> property_checker_resultt
  {
    if(cmdline.isset("bdd") || cmdline.isset("show-bdds"))
    {
      return bdd_engine(
        cmdline, transition_system, properties, message_handler);
    }
    else if(cmdline.isset("aig") || cmdline.isset("dimacs"))
    {
      // bit-level BMC
      return bit_level_bmc(
        cmdline, transition_system, properties, message_handler);
    }
    else if(cmdline.isset("k-induction"))
    {
      return k_induction(
        cmdline, transition_system, properties, message_handler);
    }
    else if(cmdline.isset("ic3"))
    {
#ifdef _WIN32
      throw ebmc_errort() << "No support for IC3 on Windows";
#else
      return ic3_engine(
        cmdline, transition_system, properties, message_handler);
#endif
    }
    else if(cmdline.isset("bound"))
    {
      // word-level BMC
      return word_level_bmc(
        cmdline, transition_system, properties, message_handler);
    }
    else
    {
      // heuristic engine selection
      return engine_heuristic(
        cmdline, transition_system, properties, message_handler);
    }
  }();

  if(result.status == property_checker_resultt::statust::VERIFICATION_RESULT)
  {
    const namespacet ns{transition_system.symbol_table};
    report_results(cmdline, result, ns, message_handler);
  }

  return result;
}

int property_checker_resultt::exit_code() const
{
  switch(status)
  {
  case statust::ERROR:
    return 10;

  case statust::SUCCESS:
    return 0;

  case statust::VERIFICATION_RESULT:
    // We return '0' if all properties are proved,
    // and '10' otherwise.
    return all_properties_proved() ? 0 : 10;
  }

  UNREACHABLE;
}
