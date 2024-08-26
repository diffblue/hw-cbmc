/*******************************************************************\

Module: Base for Verification Modules

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ebmc_base.h"

#include <util/cmdline.h>
#include <util/config.h>
#include <util/expr_util.h>
#include <util/string2int.h>

#include <solvers/prop/literal_expr.h>
#include <solvers/sat/satcheck.h>
#include <trans-netlist/compute_ct.h>
#include <trans-netlist/ldg.h>
#include <trans-netlist/trans_to_netlist.h>
#include <trans-netlist/trans_trace_netlist.h>
#include <trans-netlist/unwind_netlist.h>
#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/unwind.h>

#include "dimacs_writer.h"
#include "ebmc_error.h"
#include "ebmc_solver_factory.h"
#include "ebmc_version.h"
#include "output_file.h"
#include "report_results.h"

#include <chrono>
#include <iostream>

/*******************************************************************\

Function: ebmc_baset::ebmc_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ebmc_baset::ebmc_baset(
  const cmdlinet &_cmdline,
  ui_message_handlert &_ui_message_handler)
  : message(_ui_message_handler), cmdline(_cmdline)
{
}

/*******************************************************************\

Function: ebmc_baset::finish_bit_level_bmc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::finish_bit_level_bmc(const bmc_mapt &bmc_map, propt &solver)
{
  auto sat_start_time = std::chrono::steady_clock::now();

  message.status() << "Solving with " << solver.solver_text() << messaget::eom;

  for(propertyt &property : properties.properties)
  {
    if(property.is_disabled())
      continue;

    if(property.is_failure())
      continue;

    if(property.is_assumed())
      continue;

    message.status() << "Checking " << property.name << messaget::eom;

    literalt property_literal=!solver.land(property.timeframe_literals);
  
    bvt assumptions;
    assumptions.push_back(property_literal);

    propt::resultt prop_result = solver.prop_solve(assumptions);

    switch(prop_result)
    {
    case propt::resultt::P_SATISFIABLE:
      {
        property.refuted();
        message.result() << "SAT: counterexample found" << messaget::eom;

        namespacet ns(transition_system.symbol_table);

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
        return 2;

    default:
        message.error() << "Unexpected result from decision procedure"
                        << messaget::eom;
        return 1;
    }
  }

  auto sat_stop_time = std::chrono::steady_clock::now();

  message.statistics()
    << "Solver time: "
    << std::chrono::duration<double>(sat_stop_time - sat_start_time).count()
    << messaget::eom;

  return properties.exit_code();
}

/*******************************************************************\

Function: ebmc_baset::get_bound

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ebmc_baset::get_bound()
{
  if(!cmdline.isset("bound"))
  {
    message.warning() << "using default bound 1" << messaget::eom;
    bound=1;
    return false;
  }

  bound=unsafe_string2unsigned(cmdline.get_value("bound"));

  return false;
}

/*******************************************************************\

Function: ebmc_baset::do_bit_level_bmc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::do_bit_level_bmc(cnft &solver, bool convert_only)
{
  if(get_bound()) return 1;

  int result;

  try
  {
    bmc_mapt bmc_map;
  
    if(!convert_only)
      if(properties.properties.empty())
        throw "no properties";
      
    netlistt netlist;
    if(make_netlist(netlist))
      throw 0;

    message.status() << "Unwinding Netlist" << messaget::eom;

    bmc_map.map_timeframes(netlist, bound+1, solver);

    ::unwind(netlist, bmc_map, message, solver);

    const namespacet ns(transition_system.symbol_table);

    // convert the properties
    for(propertyt &property : properties.properties)
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

      ::unwind_property(
        netlist_property->second, bmc_map, property.timeframe_literals);

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
      result=0;
    else
    {
      result = finish_bit_level_bmc(bmc_map, solver);
      report_results(cmdline, properties, ns, message.get_message_handler());
    }
  }

  catch(const char *e)
  {
    message.error() << e << messaget::eom;
    return 10;
  }
  
  catch(const std::string &e)
  {
    message.error() << e << messaget::eom;
    return 10;
  }
  
  catch(int)
  {
    return 10;
  }  

  return result;
}

/*******************************************************************\

Function: ebmc_baset::do_bit_level_bmc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::do_bit_level_bmc()
{
  if(cmdline.isset("dimacs"))
  {
    if(cmdline.isset("outfile"))
    {
      auto outfile = output_filet{cmdline.get_value("outfile")};

      message.status() << "Writing DIMACS CNF to `" << outfile.name() << "'"
                       << messaget::eom;

      dimacs_cnf_writert dimacs_cnf_writer{
        outfile.stream(), message.get_message_handler()};

      return do_bit_level_bmc(dimacs_cnf_writer, true);
    }
    else
    {
      dimacs_cnf_writert dimacs_cnf_writer{
        std::cout, message.get_message_handler()};

      return do_bit_level_bmc(dimacs_cnf_writer, true);
    }
  }
  else
  {
    if(cmdline.isset("outfile"))
      throw ebmc_errort()
        << "Cannot write to outfile without file format option";

    satcheckt satcheck{message.get_message_handler()};

    message.status() << "Using " << satcheck.solver_text() << messaget::eom;

    return do_bit_level_bmc(satcheck, false);
  }
}
/*******************************************************************\

Function: ebmc_baset::get_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::get_properties()
{
  properties = ebmc_propertiest::from_command_line(
    cmdline, transition_system, message.get_message_handler());

  if(cmdline.isset("show-properties"))
  {
    show_properties();
    return 0;
  }

  if(cmdline.isset("json-properties"))
  {
    json_properties(cmdline.get_value("json-properties"));
    return 0;
  }

  return -1; // done
}

/*******************************************************************\

Function: ebmc_baset::show_ldg

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_baset::show_ldg(std::ostream &out)
{
  netlistt netlist;

  if(make_netlist(netlist))
    return;
  
  if(!netlist.transition.empty())
    out << "WARNING: transition constraint found!" << '\n'
        << '\n';
  
  ldgt ldg;
 
  ldg.compute(netlist);
    
  out << "Latch dependencies:" << '\n';

  for(var_mapt::mapt::const_iterator
      it=netlist.var_map.map.begin();
      it!=netlist.var_map.map.end();
      it++)
  {
    const var_mapt::vart &var=it->second;

    for(std::size_t i=0; i<var.bits.size(); i++)
    {
      if(var.is_latch())
      {
        literalt::var_not v=var.bits[i].current.var_no();

        out << "  " << it->first
            << "[" << i << "] = " << v << ":";

        const ldg_nodet &node=ldg[v];

        for(ldg_nodet::edgest::const_iterator
            i_it=node.in.begin();
            i_it!=node.in.end();
            i_it++)
          out << " " << i_it->first;

        out << '\n';
      }
    }
  }
}

/*******************************************************************\

Function: ebmc_baset::make_netlist

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ebmc_baset::make_netlist(netlistt &netlist)
{
  // make net-list
  message.status() << "Generating Netlist" << messaget::eom;

  try
  {
    convert_trans_to_netlist(
      transition_system.symbol_table,
      transition_system.main_symbol->name,
      properties.make_property_map(),
      netlist,
      message.get_message_handler());
  }
  
  catch(const std::string &error_str)
  {
    message.error() << error_str << messaget::eom;
    return true;
  }

  message.statistics() << "Latches: " << netlist.var_map.latches.size()
                       << ", nodes: " << netlist.number_of_nodes()
                       << messaget::eom;

  return false;
}

/*******************************************************************\

Function: ebmc_baset::do_compute_ct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::do_compute_ct()
{
  // make net-list
  message.status() << "Making Netlist" << messaget::eom;

  netlistt netlist;
  if(make_netlist(netlist)) return 1;

  message.status() << "Latches: " << netlist.var_map.latches.size()
                   << ", nodes: " << netlist.number_of_nodes() << messaget::eom;

  message.status() << "Making LDG" << messaget::eom;

  ldgt ldg;
  ldg.compute(netlist);

  std::cout << "CT = " << compute_ct(ldg) << '\n';
  
  return 0;
}
