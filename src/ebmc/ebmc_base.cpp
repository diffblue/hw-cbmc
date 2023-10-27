/*******************************************************************\

Module: Base for Verification Modules

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ebmc_base.h"

#include <util/cmdline.h>
#include <util/config.h>
#include <util/expr_util.h>
#include <util/find_macros.h>
#include <util/json.h>
#include <util/string2int.h>
#include <util/unicode.h>
#include <util/xml.h>
#include <util/xml_irep.h>

#include <langapi/language.h>
#include <langapi/language_util.h>
#include <langapi/mode.h>
#include <solvers/prop/literal_expr.h>
#include <trans-netlist/compute_ct.h>
#include <trans-netlist/ldg.h>
#include <trans-netlist/trans_to_netlist.h>
#include <trans-netlist/trans_trace_netlist.h>
#include <trans-netlist/unwind_netlist.h>
#include <trans-word-level/property.h>
#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/unwind.h>

#include "ebmc_error.h"
#include "ebmc_version.h"
#include "report_results.h"

#include <chrono>
#include <fstream>
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

Function: ebmc_baset::property_requires_lasso_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ebmc_baset::property_requires_lasso_constraints() const
{
  for(const auto &p : properties.properties)
    if(!p.is_disabled() && requires_lasso_constraints(p.expr))
      return true;

  return false;
}

/*******************************************************************\

Function: ebmc_baset::finish_word_level_bmc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_baset::word_level_properties(decision_proceduret &solver)
{
  const namespacet ns(transition_system.symbol_table);

  for(propertyt &property : properties.properties)
  {
    if(property.is_disabled())
      continue;

    ::property(
      property.expr,
      property.timeframe_handles,
      message.get_message_handler(),
      solver,
      bound + 1,
      ns);
  }
}

/*******************************************************************\

Function: ebmc_baset::finish_word_level_bmc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::finish_word_level_bmc(stack_decision_proceduret &solver)
{
  const namespacet ns(transition_system.symbol_table);

  // lasso constraints, if needed
  if(property_requires_lasso_constraints())
  {
    message.status() << "Adding lasso constraints" << messaget::eom;
    lasso_constraints(
      solver, bound + 1, ns, transition_system.main_symbol->name);
  }

  message.status() << "Solving with " << solver.decision_procedure_text()
                   << messaget::eom;

  auto sat_start_time = std::chrono::steady_clock::now();
  
  // Use assumptions to check the properties separately

  for(propertyt &property : properties.properties)
  {
    if(property.is_disabled())
      continue;

    message.status() << "Checking " << property.name << messaget::eom;

    auto constraint = not_exprt(conjunction(property.timeframe_handles));
    auto handle = solver.handle(constraint);
    if(handle.is_true())
      solver.push({literal_exprt(const_literal(true))});
    else if(handle.is_false())
      solver.push({literal_exprt(const_literal(false))});
    else
      solver.push({solver.handle(constraint)});

    decision_proceduret::resultt dec_result = solver();

    solver.pop();

    switch(dec_result)
    {
    case decision_proceduret::resultt::D_SATISFIABLE:
      {
        property.make_failure();
        message.result() << "SAT: counterexample found" << messaget::eom;

        property.counterexample = compute_trans_trace(
          property.timeframe_handles,
          solver,
          bound + 1,
          ns,
          transition_system.main_symbol->name);
      }
      break;

    case decision_proceduret::resultt::D_UNSATISFIABLE:
        message.result() << "UNSAT: No counterexample found within bound"
                         << messaget::eom;
        property.make_success();
        break;

    case decision_proceduret::resultt::D_ERROR:
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

  // We return '0' if the property holds,
  // and '10' if it is violated.
  return properties.property_failure() ? 10 : 0;
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

    message.status() << "Checking " << property.name << messaget::eom;

    literalt property_literal=!solver.land(property.timeframe_literals);
  
    bvt assumptions;
    assumptions.push_back(property_literal);
    solver.set_assumptions(assumptions);
  
    propt::resultt prop_result=
      solver.prop_solve();
    
    switch(prop_result)
    {
    case propt::resultt::P_SATISFIABLE:
      {
        property.make_failure();
        message.result() << "SAT: counterexample found" << messaget::eom;

        namespacet ns(transition_system.symbol_table);

        property.counterexample =
          compute_trans_trace(property.timeframe_literals, bmc_map, solver, ns);
      }
      break;

    case propt::resultt::P_UNSATISFIABLE:
        message.result() << "UNSAT: No counterexample found within bound"
                         << messaget::eom;
        property.make_success();
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

  // We return '0' if the property holds,
  // and '10' if it is violated.
  return properties.property_failure() ? 10 : 0;
}

/*******************************************************************\

Function: ebmc_baset::parse_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ebmc_baset::parse_property(
  const std::string &property)
{
  namespacet ns(transition_system.symbol_table);

  auto language = get_language_from_mode(transition_system.main_symbol->mode);

  exprt expr;
  if(language->to_expr(
       property, id2string(transition_system.main_symbol->module), expr, ns))
  {
    return true;
  }

  // We give it an implict always, as in SVA
  
  if(expr.id()!=ID_sva_always)
  {
    unary_predicate_exprt tmp(ID_sva_always, expr);
    expr.swap(tmp);
  }

  std::string expr_as_string;
  language->from_expr(expr, expr_as_string, ns);
  message.debug() << "Property: " << expr_as_string << messaget::eom;
  message.debug() << "Mode: " << transition_system.main_symbol->mode
                  << messaget::eom;

  properties.properties.push_back(propertyt());
  properties.properties.back().expr = expr;
  properties.properties.back().expr_string = expr_as_string;
  properties.properties.back().mode = transition_system.main_symbol->mode;
  properties.properties.back().location.make_nil();
  properties.properties.back().description = "command-line assertion";
  properties.properties.back().name = "command-line assertion";

  return false;
}

/*******************************************************************\

Function: ebmc_baset::get_model_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ebmc_baset::get_model_properties()
{
  if(properties.from_transition_system(
       transition_system, properties, message.get_message_handler()))
    return true;

  if(properties.select_property(cmdline, message.get_message_handler()))
    return true;

  return false;
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

Function: ebmc_baset::do_word_level_bmc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::do_word_level_bmc(
  stack_decision_proceduret &solver,
  bool convert_only)
{
  int result=0;

  try
  {
    if(cmdline.isset("max-bound"))
    {
      if(convert_only)
        throw "please set a specific bound";
        
      const std::size_t max_bound=
        unsafe_string2size_t(cmdline.get_value("max-bound"));
    
      for(bound=1; bound<=max_bound; bound++)
      {
        message.status() << "Doing BMC with bound " << bound << messaget::eom;

#if 0
        const namespacet ns(transition_system.symbol_table);
        CHECK_RETURN(trans_expr.has_value());
        ::unwind(*trans_expr, *message_handler, solver, bound+1, ns, true);
        result=finish_word_level_bmc(solver);
#endif
      }

      const namespacet ns(transition_system.symbol_table);
      report_results(cmdline, properties, ns, message.get_message_handler());
    }
    else
    {
      if(get_bound()) return 1;
    
      if(!convert_only)
        if(properties.properties.empty())
          throw "no properties";

      message.status() << "Generating Decision Problem" << messaget::eom;

      // convert the transition system
      const namespacet ns(transition_system.symbol_table);
      CHECK_RETURN(transition_system.trans_expr.has_value());
      ::unwind(
        *transition_system.trans_expr,
        message.get_message_handler(),
        solver,
        bound + 1,
        ns,
        true);

      message.status() << "Properties" << messaget::eom;

      // convert the properties
      word_level_properties(solver);

      if(convert_only)
      {
        for(propertyt &property : properties.properties)
        {
          if(!property.is_disabled())
            solver.set_to_false(conjunction(property.timeframe_handles));
        }

        result=0;
      }
      else
      {
        result = finish_word_level_bmc(solver);
        report_results(cmdline, properties, ns, message.get_message_handler());
      }
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

      ::unwind_property(
        property.expr,
        property.timeframe_literals,
        message.get_message_handler(),
        solver,
        bmc_map,
        ns);

      // freeze for incremental usage
      for(auto l : property.timeframe_literals)
        solver.set_frozen(l);
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

Function: ebmc_baset::get_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::get_properties()
{
  // Property given on command line?
  if(cmdline.isset('p'))
  {
    // NuSMV also uses -p
    if(parse_property(cmdline.get_value('p')))
      return 1;
  }
  else
  {
    // get properties from the model files
    if(get_model_properties())
      return 1;
  }

  if(cmdline.isset("show-properties"))
  {
    show_properties();
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
