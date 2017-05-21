/*******************************************************************\

Module: Main Module 

Author: Himanshu Jain, hjain@cs.cmu.edu
        Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/*

VCEGAR
Counter Example Guided Abstraction Refinement for Verilog

Copyright (C) 2002 Daniel Kroening <kroening@handshake.de>

Purpose: Counter Example Guided Abstraction refinement for Verilog

*/

#include <memory>
#include <fstream>

#include <util/config.h>
#include <util/ui_message.h>
#include <util/namespace.h>
#include <util/get_module.h>
#include <util/xml.h>
#include <util/xml_irep.h>
#include <util/std_expr.h>

#include <langapi/languages.h>
#include <langapi/mode.h>
#include <langapi/language_ui.h>
#include <langapi/language_util.h>

#include <solvers/sat/dimacs_cnf.h>
#include <solvers/sat/satcheck_minisat.h>

#include <verilog/verilog_language.h>
#include <verilog/expr2verilog.h>

//General
#include "vcegar.h"
#include "discover_predicates.h"

//Related to predicate abstraction
#include "modelchecker_smv.h"
#include "simulator.h"
#include "abstractor.h"
#include "vcegar_loop.h"
#include "refiner.h"
#include "specification.h"

class vcegart:public language_uit
{
public:
  virtual int doit();

  vcegart(const cmdlinet &_cmdline):
    language_uit("vcegar", _cmdline),
    cmdline(_cmdline)
  {
  }

protected:
  const cmdlinet &cmdline;

  var_mapt map;

  irep_idt module_identifier;
  const transt *trans_expr; // transition system expression

  concrete_transt concrete_trans;  
  specificationt user_provided_spec;
  optionst options;
  
  unsigned max_iterations()
  {
    if(cmdline.isset("i"))
      return atoi(cmdline.get_value("i"));

    return 1;    
  }

  bool get_main();

  unsigned bound;

  void get_properties_from_file();
  void get_initial_predicates();
  int pred_abs_init();
  void get_user_provided_preds();

  modelcheckert *select_modelchecker(
    const cmdlinet &cmdline,
    message_handlert &_message_handler);

  std::vector<specificationt> specs;
  std::vector<exprt> user_provided_preds;
};

/*******************************************************************\

Function: vcegart::get_main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vcegart::get_main()
{
  const std::string module=
    cmdline.isset("module")?cmdline.get_value("module"):"main";

  try
  {
    const symbolt &symbol=
      get_module(symbol_table, module, get_message_handler());

    trans_expr=&to_trans_expr(symbol.value);
    module_identifier=symbol.name;
 
    status() << "Module identifier is " << module_identifier << eom;

    if(cmdline.isset("showtrans"))
    {
      transt trans(*trans_expr);

      exprt::operandst &op=trans.operands();
      
      std::cout <<"General constrains before follow macros \n"<<op[0]<<"\n";
      std::cout <<"Initial constrains before follow macros \n"<<op[1]<<"\n";
      std::cout <<"Transition relation before follow macros \n"<<op[2]<<"\n";
      std::cout << "Operands.size "<<op.size() << "\n";

      // expand defines (macros)
      namespacet ns(symbol_table);
      ns.follow_macros(op[0]);
      ns.follow_macros(op[1]);
      ns.follow_macros(op[2]);

      std::cout <<"General constrains \n"<<op[0]<<"\n";
      std::cout <<"Initial constrains \n"<<op[1]<<"\n";
      std::cout <<"Transition relation \n"<<op[2]<<"\n";
      std::cout << "Operands.size "<<op.size() << "\n";
      return 1;
    }
  }

  catch(int e)
  {
    return true;
  }

  return false;
}

/*******************************************************************\

Function: vcegart::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int vcegart::doit()
{
  if(parse()) return 1;

  status() << "Parsing done" << eom;

  if(cmdline.isset("showparse"))
  {
    language_files.show_parse(std::cout);
    return 0;
  }

  //
  // type checking
  //

  if(typecheck()) return 2;

  status() << "typechecking done" << eom;

  // get module name

  if(get_main()) return 1;

  map.map_vars(symbol_table, module_identifier);

  if(cmdline.isset("showvarmap"))
  {
    map.output(std::cout);
    return 0;
  }

  if(cmdline.isset("showcontext"))
  {
    symbol_table.show(std::cout);
    return 0;
  }

  if(cmdline.isset("p"))
  {
    try
    {
      get_properties_from_file();
      get_initial_predicates();

      if(cmdline.isset("pred"))
        get_user_provided_preds();
          
      pred_abs_init();
    }
  
    catch(const char *e)
    {
      error() << e << eom;
      return 1;
    }

    catch(const std::string &e)
    {
      error() << e << eom;
      return 1;
    }
  }
  else if(cmdline.isset("claim"))
  {
    // get properties from model

    try
    {
      unsigned c=atoi(cmdline.get_value("claim"));
      unsigned i=0;
    
      forall_symbol_module_map(
        it,
        symbol_table.symbol_module_map, 
        module_identifier)
      {
        namespacet ns(symbol_table);
        const symbolt &symbol=ns.lookup(it->second);

        if(symbol.is_property)
        {
          i++;
          
          if(c==i)
          {
            std::string string_value=
              from_expr(ns, symbol.name, symbol.value);

            status() << "Property: " << string_value << eom;

            specs.push_back(specificationt());
            specificationt &spec=specs.back();
            spec.property_string=string_value;
            spec.property=symbol.value;
            break;
          }
        }
      }
      
      if(specs.empty())
      {
        error() << "Claim number " << c << " out of range" << eom;
        return true;
      }

      get_initial_predicates();
          
      if(cmdline.isset("pred"))
        get_user_provided_preds();
          
      pred_abs_init();
    }
  
    catch(const char *e)
    {
      error() << e << eom;
      return 1;
    }

    catch(const std::string &e)
    {
      error() << e << eom;
      return 1;
    }
  }
  else
  {
    error() << "Please specify what property to verify" << eom;
    return 1;
  }
  
  return 0;
}


/*******************************************************************\

Function: vcegart::get_initial_predicates

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vcegart::get_initial_predicates()
{
  for(std::vector<specificationt>::iterator it=specs.begin();
      it!=specs.end();
      it++)
  {
    //For predicate abstraction
    // calculationg the initial set of predicates.

    int initp;
    if(!cmdline.isset("init-pred"))
      initp = 1;
    else 
      initp=atoi(cmdline.get_value("init-pred"));
    
    switch(initp)
    {
    case 1:
      { 
        std::set<predicatet> predicate_set;
      
        int discover;
        if(!cmdline.isset("discover"))
          discover = 3;
        else 
          discover=atoi(cmdline.get_value("discover"));
  
        assert(discover==1 || discover==2 || 
               discover==3 || discover==4);

        bool dummy_isAtomic;
       
        discover_predicates(it->property, predicate_set, 3, dummy_isAtomic);

        for(std::set<predicatet>::const_iterator
            p_it=predicate_set.begin();
            p_it!=predicate_set.end();
            p_it++) 
          it->preds_from_property.push_back(*p_it);
       
        if(cmdline.isset("verbose"))
        {
          status() << "Initial set of predicates" << eom;
           
          int count =0;
          for(std::set<predicatet>::const_iterator
              p_it=predicate_set.begin();
              p_it!=predicate_set.end();
              p_it++)
          {
            count++;
            status() <<  "[" << count << "]" << expr2verilog(*p_it) << eom;
            status() << "--------------" << eom;
          }
        }
        break;
      }
      
    case 2:
      {
        status() << "Using the property itself as the initial predicate" << eom;

        exprt init_pred(it->property);
        it->preds_from_property.push_back(init_pred);
      }
    }
  }
}

/*******************************************************************\

Function: vcegart::get_properties_from_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vcegart::get_properties_from_file()
{
  std::ifstream infile(cmdline.get_value("p"));
  
  if(!infile)
    throw std::string("failed to open ")+cmdline.get_value("p");
  
  // use auto_ptr because of the exceptions
  std::auto_ptr<languaget> language(new verilog_languaget);
  
  std::string line;
  namespacet ns(symbol_table);
    
  while(std::getline(infile, line))
  {
    if(line=="") continue;
    if(line[0]=='#') continue;
    if(std::string(line, 0, 2)=="//") continue;
  
    exprt tmp_expr;


    if(language->to_expr(
         line, module_identifier,
         tmp_expr, get_message_handler(), ns))
      throw "failed to parse the property";

    exprt expr(tmp_expr);

    if(expr.type().id()!="bool")
    {
      std::string type_string;
      language->from_type(expr.type(), type_string, ns);
      throw "expected boolean expression as predicate, but got "+type_string;
    }
    
    if(cmdline.isset("verbose"))
      status() << "Added the property: " << line << eom;

    specificationt spec;
    spec.property_string = line;
    spec.property = expr;
    
    specs.push_back(spec);
  }
  
  if(cmdline.isset("verbose"))
    status() << "Total number of properties added " << specs.size() << eom;
}

/*******************************************************************\

Function: vcegart::get_user_provided_preds

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vcegart::get_user_provided_preds()
{
  std::ifstream infile(cmdline.get_value("pred"));
  
  if(!infile)
    throw std::string("failed to open ")+cmdline.get_value("pred");
  
  // use auto_ptr because of the exceptions
  std::auto_ptr<languaget> language(new verilog_languaget);
  
  namespacet ns(symbol_table);
  

  const std::string module=
    cmdline.isset("module")?cmdline.get_value("module"):"main";

  std::string modeule_indentifier;
  const symbolt &symbol=get_module(symbol_table, module, get_message_handler());
  module_identifier=symbol.name;
    
  std::string line;
  while(std::getline(infile, line))
  {
    if(line!="" && line[0]!='#' &&
       std::string(line, 0, 2)!="//")
    {
      exprt expr;
      

      if(language->to_expr(line, module_identifier, expr, get_message_handler(), ns))
        throw "failed to parse the user provided predicates";

      #if 1
      std::cout<<"The parsed predicate after conversion\n";
      std::cout <<expr<<"\n\n";
      #endif

      if(expr.type().id()!="bool")
      {
        std::string type_string;
        language->from_type(expr.type(), type_string, ns);
        throw "expected boolean expression as predicate, but got "+type_string;
      }
      
      user_provided_preds.push_back(expr);
    }
  }

  status() << "Total number of predicates added " << user_provided_preds.size() << eom;
   
  #if 1
  status() << "Predicates discovered from the predicate file are" << eom;
   
  for(unsigned i=0;i<user_provided_preds.size();i++)
  {
    status() << "[" << i << "] " << expr2verilog(user_provided_preds[i]) << eom;
    status() << "--------------" << eom;
  }
  #endif
}

/*******************************************************************\

Function: select_modelchecker

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

modelcheckert *vcegart::select_modelchecker(
  const cmdlinet &cmdline,
  message_handlert &_message_handler)
{
  std::string name=
    cmdline.isset("modelchecker")?
      cmdline.get_value("modelchecker"):"cadencesmv";

  bool verbose = cmdline.isset("verbose");
  bool claim   = cmdline.isset("claim");
  bool absref3 = cmdline.isset("absref3");

  if (name=="nusmv")
    return new modelchecker_smvt(_message_handler,  modelchecker_smvt::NUSMV, verbose, claim, false);
  else if (name=="cadencesmv")
    return new modelchecker_smvt(_message_handler,  modelchecker_smvt::CADENCE_SMV, verbose, claim, absref3);
  else
    throw "unknown modelchecker: "+name;
}

/*******************************************************************\

Function: vcegart::pred_abs_init

  Inputs:

 Outputs:

 Purpose: Starts the predicate abstraction routine.

\*******************************************************************/

int vcegart::pred_abs_init()
{
  config.set(cmdline);

  // set the same verbosity for all
  int verbosity=4;

  if(cmdline.isset("v")) 
    verbosity = atoi(cmdline.get_value("v"));
  

  //Parsing and typecheking has already been done
  //Properties have been collected
  //Initial predicates have been obtained 
  //So just give these to prepare.  
  concrete_trans.var_map = map;

  //Currently we doing the abstraction on monolithic
  //transition relation. So there is only one thread 
  
  concrete_trans.trans_expr = *trans_expr;

  //threads to create
  int num_threads = 1;
  
  if (cmdline.isset("num-threads"))
    {
      num_threads = atoi(cmdline.get_value("num-threads"));
      
      if (num_threads <= 0)
	throw "Expected number of threads to be greater than zero\n";
    }
  //For each property start start new predicate abstraction

  for(std::vector<specificationt>::const_iterator 
      it=specs.begin();
      it!=specs.end();
      it++)
  {
    user_provided_spec = *it;
    
    status() << "Verififying property: " << it->property_string << eom;
    
    try
    {
      // The tools we need
      
      // finds predicates
      refinert refiner(get_message_handler(), cmdline);
      
      // calculates abstract program
      abstractort abstractor(get_message_handler(), cmdline);
      
      // model checking engine
      std::auto_ptr<modelcheckert> 
        modelchecker(select_modelchecker(cmdline, get_message_handler()));      
      
      // checks counterexamples
      simulatort simulator(get_message_handler(), cmdline, module_identifier, num_threads); 
      
      //controls various components of abstraction refinement loop
      vcegar_loopt vcegar_loop(
        concrete_trans,
        user_provided_spec,
        symbol_table,
        abstractor,
        refiner,
        *modelchecker,
        simulator,
        get_message_handler(), // as a message handler
        max_iterations(),
        cmdline,
        user_provided_preds,
        get_ui());
      
      // set their verbosity -- all the same for now
      refiner.set_verbosity(verbosity);
      abstractor.set_verbosity(verbosity);
      modelchecker->set_verbosity(verbosity);
      simulator.set_verbosity(verbosity);
      vcegar_loop.set_verbosity(verbosity);
      
      // Get going
      vcegar_loop.go();
    }
    
    catch(const char *e)
    {
      error() << e << eom;
      return 1;
    }
    
    catch(const std::string e)
    {
      error() << e << eom;
      return 1;
    }
  }

  return 0;
}

/*******************************************************************\

Function: do_vcegar

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int do_vcegar(const cmdlinet &cmdline)
{
  vcegart vcegar(cmdline);

  return vcegar.doit();
}
