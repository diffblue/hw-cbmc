/*******************************************************************\

Module: Base for Verification Modules

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ebmc_base.h"
#include "ebmc_version.h"

#include <trans-netlist/trans_trace_netlist.h>
#include <trans-netlist/ldg.h>
#include <trans-netlist/trans_to_netlist.h>
#include <trans-netlist/unwind_netlist.h>
#include <trans-netlist/compute_ct.h>

#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/property.h>
#include <trans-word-level/unwind.h>
#include <trans-word-level/show_modules.h>

#include <langapi/language.h>
#include <langapi/language_util.h>
#include <langapi/mode.h>

#include <solvers/prop/literal_expr.h>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/expr_util.h>
#include <util/find_macros.h>
#include <util/get_module.h>
#include <util/string2int.h>
#include <util/unicode.h>
#include <util/xml.h>
#include <util/xml_irep.h>

#include <chrono>
#include <fstream>
#include <iostream>

/*******************************************************************\

Function: make_next_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void make_next_state(exprt &expr) {
  for (auto &sub_expression : expr.operands())
    make_next_state(sub_expression);

  if(expr.id()==ID_symbol)
    expr.id(ID_next_symbol);
}

/*******************************************************************\

Function: ebmc_baset::ebmc_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ebmc_baset::ebmc_baset(const cmdlinet &_cmdline,
                       ui_message_handlert &_ui_message_handler)
    : messaget(_ui_message_handler), symbol_table{}, cmdline(_cmdline),
      main_symbol(NULL) {
  if(cmdline.isset("verbosity"))
    message_handler->set_verbosity(
        unsafe_string2unsigned(cmdline.get_value("verbosity")));
  else
    message_handler->set_verbosity(messaget::M_STATUS); // default
}

/*******************************************************************\

Function: ebmc_baset::finish_word_level_bmc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_baset::word_level_properties(decision_proceduret &solver)
{
  const namespacet ns(symbol_table);

  for(propertyt &property : properties)
  {
    if(property.is_disabled())
      continue;

    ::property(
      property.expr,
      property.timeframe_handles,
      get_message_handler(),
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
  status() << "Solving with "
           << solver.decision_procedure_text() << eom;

  auto sat_start_time = std::chrono::steady_clock::now();
  
  // Use assumptions to check the properties separately
  
  for(propertyt &property : properties)
  {
    if(property.is_disabled())
      continue;
    
    status() << "Checking " << property.name << eom;

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
        result() << "SAT: counterexample found" << messaget::eom;

        namespacet ns(symbol_table);

        property.counterexample = compute_trans_trace(
          property.timeframe_handles, solver, bound + 1, ns, main_symbol->name);
      }
      break;

    case decision_proceduret::resultt::D_UNSATISFIABLE:
      result() << "UNSAT: No counterexample found within bound"
               << messaget::eom;
      property.make_success();
      break;

    case decision_proceduret::resultt::D_ERROR:
      error() << "Error from decision procedure" << messaget::eom;
      return 2;

    default:
      error() << "Unexpected result from decision procedure" << messaget::eom;
      return 1;
    }
  }

  auto sat_stop_time = std::chrono::steady_clock::now();

  statistics()
     << "Solver time: "
     << std::chrono::duration<double>(sat_stop_time-sat_start_time).count()
     << eom;

  // We return '0' if the property holds,
  // and '10' if it is violated.
  return property_failure() ? 10 : 0;
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

  status() << "Solving with " << solver.solver_text() << eom;

  for(propertyt &property : properties)
  {
    if(property.is_disabled())
      continue;

    status() << "Checking " << property.name << messaget::eom;

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
        result() << "SAT: counterexample found" << messaget::eom;

        namespacet ns(symbol_table);

        property.counterexample =
          compute_trans_trace(property.timeframe_literals, bmc_map, solver, ns);
      }
      break;

    case propt::resultt::P_UNSATISFIABLE:
      result() << "UNSAT: No counterexample found within bound"
               << messaget::eom;
      property.make_success();
      break;

    case propt::resultt::P_ERROR:
      error() << "Error from decision procedure" << messaget::eom;
      return 2;

    default:
      error() << "Unexpected result from decision procedure" << messaget::eom;
      return 1;
    }
  }

  auto sat_stop_time = std::chrono::steady_clock::now();  
    
  statistics()
    << "Solver time: "
    << std::chrono::duration<double>(sat_stop_time-sat_start_time).count()
    << eom;

  // We return '0' if the property holds,
  // and '10' if it is violated.
  return property_failure()?10:0;
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

  auto language = get_language_from_mode(main_symbol->mode);

  exprt expr;
  if(language->to_expr(
    property,
    id2string(main_symbol->module),
    expr,
    ns))
    return true;

  // We give it an implict always, as in SVA
  
  if(expr.id()!=ID_sva_always)
  {
    unary_predicate_exprt tmp(ID_sva_always, expr);
    expr.swap(tmp);
  }

  std::string expr_as_string;
  language->from_expr(expr, expr_as_string, ns);
  debug() << "Property: " << expr_as_string << eom;
  debug() << "Mode: " << main_symbol->mode << eom;

  properties.push_back(propertyt());
  properties.back().expr=expr;
  properties.back().expr_string=expr_as_string;
  properties.back().mode=main_symbol->mode;
  properties.back().location.make_nil();
  properties.back().description="command-line assertion";
  properties.back().name="command-line assertion";
  
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
  for(auto it=symbol_table.symbol_module_map.lower_bound(main_symbol->name);
      it!=symbol_table.symbol_module_map.upper_bound(main_symbol->name);
      it++)
  {
    namespacet ns(symbol_table);
    const symbolt &symbol=ns.lookup(it->second);

    if(symbol.is_property)
    {
      try
      {
        std::string value_as_string=
          from_expr(ns, symbol.name, symbol.value);

        debug() << "Property: " << value_as_string << eom;

        properties.push_back(propertyt());
        properties.back().number=properties.size()-1;

        if(symbol.pretty_name.empty())
          properties.back().name=symbol.name;
        else
          properties.back().name=symbol.pretty_name;

        properties.back().expr=symbol.value;
        properties.back().location=symbol.location;
        properties.back().expr_string=value_as_string;
        properties.back().mode=symbol.mode;
        properties.back().description=id2string(symbol.location.get_comment());
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
    std::string property=cmdline.get_value("property");

    for(auto & p : properties)
      p.status=propertyt::statust::DISABLED;
      
    bool found=false;

    for(auto & p : properties)
      if(p.name==property)
      {
        found=true;
        p.status=propertyt::statust::UNKNOWN;
        break;
      }
    
    if(!found)
    {
      error() << "Property " << property << " not found" << eom;
      return true;
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
  std::string top_module;
  
  if(cmdline.isset("module"))
    top_module=cmdline.get_value("module");
  else if(cmdline.isset("top"))
    top_module=cmdline.get_value("top");

  try
  {
    main_symbol=&get_module(symbol_table, top_module, get_message_handler());
    trans_expr=to_trans_expr(main_symbol->value);
  }

  catch(int e)
  {
    return true;
  }

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
        status() << "Doing BMC with bound " << bound << eom;

#if 0
        const namespacet ns(symbol_table);
        CHECK_RETURN(trans_expr.has_value());
        ::unwind(*trans_expr, *message_handler, solver, bound+1, ns, true);
        result=finish_word_level_bmc(solver);
#endif
      }

      report_results();
    }
    else
    {
      if(get_bound()) return 1;
    
      if(!convert_only)
        if(properties.empty())
          throw "no properties";

      status() << "Generating Decision Problem" << eom;

      const namespacet ns(symbol_table);

      // convert the transition system
      CHECK_RETURN(trans_expr.has_value());
      ::unwind(*trans_expr, *message_handler, solver, bound + 1, ns, true);

      status() << "Properties" << eom;

      // convert the properties
      word_level_properties(solver);

      if(convert_only)
      {
        for(propertyt &property : properties)
        {
          if(!property.is_disabled())
            solver.set_to_false(conjunction(property.timeframe_handles));
        }

        result=0;
      }
      else
      {
        result = finish_word_level_bmc(solver);
        report_results();
      }
    }
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
      if(properties.empty())
        throw "no properties";
      
    netlistt netlist;
    if(make_netlist(netlist))
      throw 0;

    status() << "Unwinding Netlist" << eom;
    
    bmc_map.map_timeframes(netlist, bound+1, solver);

    ::unwind(netlist, bmc_map, *this, solver);

    // convert the properties
    for(propertyt &property : properties)
    {
      if(property.is_disabled())
        continue;

      const namespacet ns(symbol_table);

      ::unwind_property(
        property.expr,
        property.timeframe_literals,
        get_message_handler(),
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
      report_results();
    }
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

Function: ebmc_baset::preprocess

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::preprocess()
{
  if(cmdline.args.size() != 1)
  {
    error() << "please give exactly one file to preprocess" << eom;
    return 1;
  }

  const auto &filename = cmdline.args.front();

#ifdef _MSC_VER
  std::ifstream infile(widen(filename));
#else
  std::ifstream infile(filename);
#endif

  if(!infile)
  {
    error() << "failed to open input file `" << filename << "'" << eom;
    return 1;
  }

  auto language = get_language_from_filename(filename);

  if(language == nullptr)
  {
    source_locationt location;
    location.set_file(filename);
    error().source_location = location;
    error() << "failed to figure out type of file" << eom;
    return 1;
  }

  language->set_message_handler(get_message_handler());

  if(language->preprocess(infile, filename, std::cout))
  {
    error() << "PREPROCESSING FAILED" << eom;
    return 1;
  }

  return 0;
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

  if(cmdline.isset("preprocess"))
    return preprocess();

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
    show_modules(symbol_table,
                 static_cast<ui_message_handlert *>(message_handler)->get_ui());
    return 0;
  }

  if(cmdline.isset("show-symbol-table"))
  {
    std::cout << symbol_table;
    return 0;
  }

  // get module name

  if(get_main()) return 1;

  if(cmdline.isset("show-varmap"))
  {
    netlistt netlist;
    if(make_netlist(netlist)) return 1;
    netlist.var_map.output(std::cout);
    return 0;
  }

  if(cmdline.isset("show-ldg"))
  {
    show_ldg(std::cout);
    return 0;
  }
  
  // --reset given?
  if(cmdline.isset("reset"))
  {
    namespacet ns(symbol_table);
    exprt reset_constraint=to_expr(ns, main_symbol->name, cmdline.get_value("reset"));

    // true in initial state
    CHECK_RETURN(trans_expr.has_value());
    transt new_trans_expr = *trans_expr;
    new_trans_expr.init() = and_exprt(new_trans_expr.init(), reset_constraint);

    // and not anymore afterwards
    exprt reset_next_state=reset_constraint;
    make_next_state(reset_next_state);

    new_trans_expr.trans() =
        and_exprt(new_trans_expr.trans(), not_exprt(reset_next_state));
    *trans_expr = new_trans_expr;
  }

  // Property given on command line?
  if(cmdline.isset('p'))
  {
    // NuSMV also uses -p
    if(parse_property(cmdline.get_value('p')))
      return 1;
  }
  else
  {
    // get properties from file
    if(get_model_properties())
      return 1;
  }

  if(cmdline.isset("show-properties"))
  {
    show_properties();
    return 0;
  }

  if(cmdline.isset("show-netlist"))
  {
    netlistt netlist;
    if(make_netlist(netlist)) return 1;
    netlist.print(std::cout);
    return 0;
  }
  
  if(cmdline.isset("smv-netlist"))
  {
    netlistt netlist;
    if(make_netlist(netlist)) return 1;
    std::cout << "-- Generated by EBMC " << EBMC_VERSION << '\n';
    std::cout << "-- Generated from " << main_symbol->name << '\n';
    std::cout << '\n';
    netlist.output_smv(std::cout);
    return 0;
  }
  
  if(cmdline.isset("dot-netlist"))
  {
    netlistt netlist;
    if(make_netlist(netlist)) return 1;
    std::cout << "digraph netlist {\n";
    netlist.output_dot(std::cout);
    std::cout << "}\n";
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
  status() << "Generating Netlist" << eom;

  try
  {
    convert_trans_to_netlist(
      symbol_table, main_symbol->name,
      netlist, get_message_handler());
  }
  
  catch(const std::string &error_str)
  {
    error() << error_str << eom;
    return true;
  }

  statistics() << "Latches: " << netlist.var_map.latches.size()
               << ", nodes: " << netlist.number_of_nodes() << eom;
           
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
  status() << "Making Netlist" << eom;

  netlistt netlist;
  if(make_netlist(netlist)) return 1;

  status() << "Latches: " << netlist.var_map.latches.size()
           << ", nodes: " << netlist.number_of_nodes() << eom;

  status() << "Making LDG" << eom;
  
  ldgt ldg;
  ldg.compute(netlist);

  std::cout << "CT = " << compute_ct(ldg) << '\n';
  
  return 0;
}

/*******************************************************************\

Function: ebmc_baset::report_results

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_baset::report_results()
{
  const namespacet ns(symbol_table);

  if (static_cast<ui_message_handlert *>(message_handler)->get_ui() ==
      ui_message_handlert::uit::XML_UI) {
    for(const propertyt &property : properties)
    {
      if(property.status==propertyt::statust::DISABLED)
        continue;
        
      xmlt xml_result("result");
      xml_result.set_attribute("property", id2string(property.name));
      
      switch(property.status)
      {
      case propertyt::statust::SUCCESS: xml_result.set_attribute("status", "SUCCESS"); break;
      case propertyt::statust::FAILURE: xml_result.set_attribute("status", "FAILURE"); break;
      case propertyt::statust::UNKNOWN: xml_result.set_attribute("status", "UNKNOWN"); break;
      case propertyt::statust::DISABLED:;
      }
      
      if(property.is_failure())
        convert(ns, property.counterexample, xml_result.new_element());

      std::cout << xml_result << '\n' << std::flush;
    }
  }
  else
  {
    status() << eom;
    status() << "** Results:" << eom;

    for(const propertyt &property : properties)
    {
      if(property.status==propertyt::statust::DISABLED)
        continue;
      
      status() << "[" << property.name << "] "
               << property.expr_string << ": ";

      switch(property.status)
      {
      case propertyt::statust::SUCCESS: status() << "SUCCESS"; break;
      case propertyt::statust::FAILURE: status() << "FAILURE"; break;
      case propertyt::statust::UNKNOWN: status() << "UNKNOWN"; break;
      case propertyt::statust::DISABLED:;
      }
               
      status() << eom;
      
      if(property.is_failure() &&
         cmdline.isset("trace"))
      {
        status() << "Counterexample:\n" << eom;
        show_trans_trace(
            property.counterexample, *this, ns,
            static_cast<ui_message_handlert *>(message_handler)->get_ui());
      }
    }
  }

  if(cmdline.isset("vcd"))
  {
    for(const propertyt &property : properties)
    {
      if(property.is_failure())
      {
        std::string vcdfile=cmdline.get_value("vcd");
        #ifdef _MSC_VER
        std::ofstream vcd(widen(vcdfile));
        #else    
        std::ofstream vcd(vcdfile);
        #endif

        show_trans_trace_vcd(
          property.counterexample,
          *this, // message
          ns,
          vcd);

        break;
      }
    }
  }

}

bool ebmc_baset::parse() {
  for (unsigned i = 0; i < cmdline.args.size(); i++) {
    if (parse(cmdline.args[i]))
      return true;
  }
  return false;
}

bool ebmc_baset::parse(const std::string &filename) {
#ifdef _MSC_VER
  std::ifstream infile(widen(filename));
#else
  std::ifstream infile(filename);
#endif

  if (!infile) {
    error() << "failed to open input file `" << filename << "'" << eom;
    return true;
  }

  auto &lf = language_files.add_file(filename);
  lf.filename = filename;
  lf.language = get_language_from_filename(filename);

  if (lf.language == nullptr) {
    source_locationt location;
    location.set_file(filename);
    error().source_location = location;
    error() << "failed to figure out type of file" << eom;
    return true;
  }

  languaget &language = *lf.language;
  language.set_message_handler(get_message_handler());

  status() << "Parsing " << filename << eom;

  if (language.parse(infile, filename)) {
    if (static_cast<ui_message_handlert *>(message_handler)->get_ui() ==
        ui_message_handlert::uit::PLAIN)
      std::cerr << "PARSING ERROR\n";

    return true;
  }

  lf.get_modules();

  return false;
}

bool ebmc_baset::typecheck() {
  status() << "Converting" << eom;

  if (language_files.typecheck(symbol_table, *message_handler)) {
    error() << "CONVERSION ERROR" << eom;
    return true;
  }

  return false;
}
