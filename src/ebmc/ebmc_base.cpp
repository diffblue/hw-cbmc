/*******************************************************************\

Module: Base for Verification Modules

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <iostream>

#include <util/time_stopping.h>
#include <util/get_module.h>
#include <util/xml.h>
#include <util/find_macros.h>
#include <util/xml_irep.h>
#include <util/config.h>
#include <util/cmdline.h>
#include <util/string2int.h>

#include <solvers/flattening/boolbv.h>
#include <trans/unwind.h>
#include <trans/property.h>
#include <trans/trans_trace.h>
#include <trans/show_modules.h>
#include <trans/ldg.h>
#include <trans/netlist_trans.h>
#include <trans/unwind_netlist.h>
#include <langapi/language_util.h>
#include <langapi/mode.h>
#include <langapi/languages.h>

#include "ebmc_base.h"
#include "version.h"

/*******************************************************************\

Function: ebmc_baset::ebmc_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ebmc_baset::ebmc_baset(const cmdlinet &_cmdline):
  language_uit("EBMC " EBMC_VERSION, _cmdline),
  cmdline(_cmdline),
  main_symbol(NULL),
  trans_expr(NULL)
{
  ui_message_handler.set_verbosity(cmdline.isset("verbose")?9:4);
}

/*******************************************************************\

Function: ebmc_baset::show_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_baset::show_trace(const trans_tracet &trans_trace)
{
  namespacet ns(symbol_table);

  if(cmdline.isset("vcd"))
  {
    std::string vcdfile=cmdline.get_value("vcd");
    std::ofstream vcd(vcdfile.c_str());

    show_trans_trace_vcd(
      trans_trace,
      *this, // message
      ns,
      vcd);
  }
  else
  {
    if(get_ui()==ui_message_handlert::PLAIN)
      result() << "Counterexample:\n" << eom;
      
    show_trans_trace(
      trans_trace,
      *this, // message
      ns,
      get_ui());
  }
}

/*******************************************************************\

Function: ebmc_baset::finish

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::finish(prop_convt &solver)
{
  status() << "Solving with "
           << solver.decision_procedure_text() << eom;

  absolute_timet sat_start_time=current_time();
  
  decision_proceduret::resultt dec_result=
    solver.dec_solve();
  
  status() << "Solver time: " << (current_time()-sat_start_time)
           << eom;

  switch(dec_result)
  {
  case decision_proceduret::D_SATISFIABLE:
    {
      result() << "SAT: bug found" << eom;
      
      namespacet ns(symbol_table);
      trans_tracet trans_trace;
  
      compute_trans_trace(
        prop_expr_list,
        prop_bv,
        solver,
        bound+1,
        ns,
        main_symbol->name,
        trans_trace);
      
      show_trace(trans_trace);
      report_failure();
    }
    break;

  case decision_proceduret::D_UNSATISFIABLE:
    result() << "UNSAT: No bug found within bound" << eom;
    report_success();
    break;

  case decision_proceduret::D_ERROR:
    error() << "Error from decision procedure" << eom;
    return 2;

  default:
    error() << "Unexpected result from decision procedure" << eom;
    return 1;
  }

  return 0;
}

/*******************************************************************\

Function: ebmc_baset::finish

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::finish(const bmc_mapt &bmc_map, propt &solver)
{
  absolute_timet sat_start_time=current_time();
  
  status() << "Solving with " << solver.solver_text() << eom;

  propt::resultt prop_result=
    solver.prop_solve();
  
  status() << "Solver time: " << (current_time()-sat_start_time)
           << eom;

  switch(prop_result)
  {
  case propt::P_SATISFIABLE:
    {
      result() << "SAT: bug found" << eom;
      
      namespacet ns(symbol_table);
      trans_tracet trans_trace;

      compute_trans_trace(
        prop_bv,
        bmc_map,
        solver,
        ns,
        trans_trace);

      show_trace(trans_trace);
      report_failure();
    }
    break;

  case propt::P_UNSATISFIABLE:
    result() << "UNSAT: No bug found within bound" << eom;
    report_success();
    break;

  case propt::P_ERROR:
    error() << "Error from decision procedure" << eom;
    return 2;

  default:
    error() << "Unexpected result from decision procedure" << eom;
    return 1;
  }

  return 0;
}

/*******************************************************************\

Function: ebmc_baset::unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_baset::unwind(decision_proceduret &solver)
{
  unwind(solver, bound+1, true);
}

/*******************************************************************\

Function: ebmc_baset::unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_baset::unwind(
  decision_proceduret &solver,
  unsigned _bound,
  bool initial_state)
{
  const namespacet ns(symbol_table);
  ::unwind(*trans_expr, *this, solver, _bound, ns, initial_state);
}

/*******************************************************************\

Function: ebmc_baset::check_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_baset::check_property(prop_convt &solver, bool convert_only)
{
  if(!convert_only)
    if(properties.empty())
      throw "no properties";

  status() << "Generating Decision Problem" << eom;

  unwind(solver);

  namespacet ns(symbol_table);

  property(
    prop_expr_list,
    prop_bv,
    *this, // message
    solver,
    bound+1,
    ns);
}

/*******************************************************************\

Function: ebmc_baset::check_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_baset::check_property(bmc_mapt &bmc_map, cnft &solver, bool convert_only)
{
  if(!convert_only)
    if(properties.empty())
      throw "no properties";
    
  netlistt netlist;
  make_netlist(netlist);

  status() << "Unwinding Netlist" << eom;
  
  bmc_map.map_timeframes(netlist, bound+1, solver);

  ::unwind(netlist, bmc_map, *this, solver);
  ::unwind_property(netlist, bmc_map, *this, prop_bv, solver);
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
  namespacet ns(symbol_table);

  languagest languages(ns, 
    get_language_from_mode(main_symbol->mode));

  exprt expr;
  if(languages.to_expr(
    property,
    id2string(main_symbol->module),
    expr))
    return true;

  // make it AGp
  exprt tmp("AG", typet("bool"));
  tmp.move_to_operands(expr);
  expr.swap(tmp);

  std::string string_value;
  languages.from_expr(expr, string_value);
  status() << "Property: " << string_value << eom;
  status() << "Mode: " << main_symbol->mode << eom;

  prop_expr_list.push_back(exprt());
  prop_expr_list.back()=expr;
  
  properties.push_back(propertyt());
  properties.back().expr=expr;
  properties.back().expr_string=string_value;
  properties.back().mode=main_symbol->mode;
  properties.back().location.make_nil();
  properties.back().description="command-line assertion";
  
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
  forall_symbol_module_map(
    it,
    symbol_table.symbol_module_map, 
    main_symbol->name)
  {
    namespacet ns(symbol_table);
    const symbolt &symbol=ns.lookup(it->second);

    if(symbol.is_property)
    {
      try
      {
        std::string string_value=
          from_expr(ns, symbol.name, symbol.value);

        status() << "Property: " << string_value << eom;

        prop_expr_list.push_back(symbol.value);

        properties.push_back(propertyt());
        properties.back().expr=symbol.value;
        properties.back().location=symbol.location;
        properties.back().expr_string=string_value;
        properties.back().mode=symbol.mode;
        properties.back().description="assertion "+id2string(symbol.display_name());
      }
      
      catch(const char *e)
      {
        error() << e << eom;
        return true;
      }
      
      catch(const std::string &e)
      {
        error() << e << eom;
        return true;
      }
      
      catch(int)
      {
        return true;
      }  

    }
  }
  
  if(cmdline.isset("property"))
  {
    unsigned c=unsafe_string2unsigned(cmdline.get_value("property"));
    if(c<1 || c>properties.size())
    {
      error() << "Property number " << c << " out of range" << eom;
      return true;
    }

    unsigned p_nr=1;
    for(prop_expr_listt::iterator
        it=prop_expr_list.begin();
        it!=prop_expr_list.end();
        it++, p_nr++)
    {
      if(p_nr!=c) it->make_true();
    }
  }
  
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
    warning() << "using default bound 1" << eom;
    bound=1;
    return false;
  }

  bound=unsafe_string2unsigned(cmdline.get_value("bound"));

  if(bound<1)
  {
    error() << "must provide bound greater than zero" << eom;
    return true;
  }

  return false;
}

/*******************************************************************\

Function: ebmc_baset::get_main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ebmc_baset::get_main()
{
  const std::string module=
    cmdline.get_value("module");

  try
  {
    main_symbol=&get_module(symbol_table, module, get_message_handler());
    trans_expr=&to_trans_expr(main_symbol->value);
  }

  catch(int e)
  {
    return true;
  }

  return false;
}

/*******************************************************************\

Function: ebmc_baset::do_ebmc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::do_ebmc(prop_convt &solver, bool convert_only)
{
  solver.set_message_handler(get_message_handler());

  if(get_bound()) return 1;
  
  int result;

  try
  {
    check_property(solver, convert_only);

    if(convert_only)
      result=0;
    else
      result=finish(solver);
  }
  
  catch(const char *e)
  {
    error() << e << eom;
    return 10;
  }
  
  catch(const std::string &e)
  {
    error() << e << eom;
    return 10;
  }
  
  catch(int)
  {
    return 10;
  }  

  return result;
}

/*******************************************************************\

Function: ebmc_baset::do_ebmc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::do_ebmc(cnft &solver, bool convert_only)
{
  solver.set_message_handler(get_message_handler());

  if(get_bound()) return 1;

  int result;

  try
  {
    bmc_mapt bmc_map;
  
    check_property(bmc_map, solver, convert_only);
    
    if(convert_only)
      result=0;
    else
      result=finish(bmc_map, solver);
  }

  catch(const char *e)
  {
    error() << e << eom;
    return 10;
  }
  
  catch(const std::string &e)
  {
    error() << e << eom;
    return 10;
  }
  
  catch(int)
  {
    return 10;
  }  

  return result;
}

/*******************************************************************\

Function: ebmc_baset::report_success

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_baset::report_success()
{
  status() << "VERIFICATION SUCCESSFUL" << eom;

  switch(get_ui())
  {
  case ui_message_handlert::PLAIN:
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="SUCCESS";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;
    
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: ebmc_baset::report_failure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_baset::report_failure()
{
  status() << "VERIFICATION FAILED" << eom;

  switch(get_ui())
  {
  case ui_message_handlert::PLAIN:
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="FAILURE";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;
    
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: ebmc_baset::get_model

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::get_model()
{
  // do -I
  if(cmdline.isset('I'))
    config.verilog.include_paths=cmdline.get_values('I');

  //
  // parsing
  //

  if(parse()) return 1;

  if(cmdline.isset("show-parse"))
  {
    language_files.show_parse(std::cout);
    return 0;
  }

  //
  // type checking
  //

  if(typecheck()) 
    return 2;

  if(cmdline.isset("show-modules"))
  {
    show_modules(symbol_table, get_ui());
    return 0;
  }

  // get module name

  if(get_main()) return 1;

  if(cmdline.isset("show-varmap"))
  {
    netlistt netlist;
    make_netlist(netlist);
    netlist.var_map.output(std::cout);
    return 0;
  }

  if(cmdline.isset("show-ldg"))
  {
    show_ldg(std::cout);
    return 0;
  }

  // get properties
  if(cmdline.isset("property"))
  {
    if(parse_property(cmdline.get_value("property")))
      return 1;
  }
  else
  {
    // get properties from file
    if(get_model_properties())
      return 1;
  }

  if(cmdline.isset("show-netlist"))
  {
    netlistt netlist;
    make_netlist(netlist);
    netlist.print(std::cout);
    return 0;
  }
  
  if(cmdline.isset("smv-netlist"))
  {
    netlistt netlist;
    make_netlist(netlist);
    std::cout << "-- Generated by EBMC " << EBMC_VERSION << '\n';
    std::cout << "-- Generated from " << main_symbol->name << '\n';
    std::cout << '\n';
    netlist.output_smv(std::cout);
    return 0;
  }
  
  if(cmdline.isset("dot-netlist"))
  {
    netlistt netlist;
    make_netlist(netlist);
    std::cout << "digraph netlist {\n";
    netlist.output_dot(std::cout);
    std::cout << "}\n";
    return 0;
  }
  
  if(cmdline.isset("show-properties"))
  {
    show_properties();
    return 0;
  }
      
  return -1; // done with the model
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

  make_netlist(netlist);
  
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

    for(unsigned i=0; i<var.bits.size(); i++)
    {
      if(var.is_latch())
      {
        unsigned v=var.bits[i].current.var_no();

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

void ebmc_baset::make_netlist(netlistt &netlist)
{
  // make net-list
  status() << "Generating Netlist" << eom;

  try
  {
    convert_trans_to_netlist(
      symbol_table, main_symbol->name, prop_expr_list, netlist, *this);
  }
  
  catch(const std::string &error_str)
  {
    error() << error_str << eom;
    return;
  }

  status() << "Latches: " << netlist.var_map.latches.size()
           << ", nodes: " << netlist.number_of_nodes() << eom;
}
