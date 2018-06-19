/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/config.h>
#include <util/get_module.h>
#include <util/string2int.h>

#include <goto-programs/show_properties.h>
#include <goto-programs/set_properties.h>
#include <trans-word-level/show_modules.h>
#include <cbmc/version.h>
#include <cbmc/cbmc_solvers.h>
#include <langapi/mode.h>

#include "hw_cbmc_parse_options.h"
//#include "hw_bmc.h"
#include "map_vars.h"
#include "gen_interface.h"

/*******************************************************************\

Function: hw_cbmc_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int hw_cbmc_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << std::endl;
    return 0;
  }

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);

  eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_STATISTICS, ui_message_handler);

  //
  // Print a banner
  //
  status() << "HW-CBMC version " CBMC_VERSION << eom;

  register_languages();

  if(cmdline.isset("preprocess"))
  {
    preprocessing();
    return 0;
  }

  if(cmdline.isset("vcd"))
    options.set_option("vcd", cmdline.get_value("vcd"));

  symbol_tablet symbol_table;

  cbmc_solverst cbmc_solvers(options, symbol_table, ui_message_handler);
  cbmc_solvers.set_ui(ui_message_handler.get_ui());
  std::unique_ptr<cbmc_solverst::solvert> cbmc_solver;
  
  try
  {
    cbmc_solver=cbmc_solvers.get_solver();
  }
  
  catch(const char *error_msg)
  {
    error() << error_msg << eom;
    return 1;
  }

  #if 0
  prop_convt &prop_conv=cbmc_solver->prop_conv();
  hw_bmct hw_bmc(options, symbol_table, ui_message_handler, prop_conv);

  goto_functionst goto_functions;

  int get_goto_program_ret=get_goto_program(
    options, hw_bmc.bmc_constraints, goto_functions);
  if(get_goto_program_ret!=-1)
    return get_goto_program_ret;

  hw_bmc.unwind_no_timeframes=get_bound();
  hw_bmc.unwind_module=get_top_module();

  label_properties(goto_functions);

  if(cmdline.isset("show-properties"))
  {
    const namespacet ns(symbol_table);
    show_properties(ns, get_ui(), goto_functions);
    return 0;
  }

  if(set_properties(goto_functions))
    return 7;

  // do actual BMC
  return do_bmc(hw_bmc, goto_functions);
  #endif

  return false;
}

/*******************************************************************\

Function: hw_cbmc_parse_optionst::get_top_module

  Inputs:

 Outputs:

 Purpose: add additional (synchonous) modules

\*******************************************************************/

irep_idt hw_cbmc_parse_optionst::get_top_module()
{
  std::string top_module;

  if(cmdline.isset("module"))
    top_module=cmdline.get_value("module");
  else if(cmdline.isset("top"))
    top_module=cmdline.get_value("top");

  if(top_module=="")
    return irep_idt();

  return get_module(
    goto_model.symbol_table, top_module, get_message_handler()).name;
}

/*******************************************************************\

Function: hw_cbmc_parse_optionst::get_bound

  Inputs:

 Outputs:

 Purpose: add additional (synchonous) modules

\*******************************************************************/

unsigned hw_cbmc_parse_optionst::get_bound()
{
  if(cmdline.isset("bound"))
    return safe_string2unsigned(cmdline.get_value("bound"))+1;
  else
    return 1;
}

/*******************************************************************\

Function: hw_cbmc_parse_optionst::get_modules

  Inputs:

 Outputs:

 Purpose: add additional (synchonous) modules

\*******************************************************************/

int hw_cbmc_parse_optionst::get_modules(
  std::list<exprt> &bmc_constraints)
{
  //
  // unwinding of transition systems
  //

  irep_idt top_module=get_top_module();

  if(!top_module.empty())
  {
    try
    {
      if(cmdline.isset("gen-interface"))
      {
        const symbolt &symbol=
          namespacet(goto_model.symbol_table).lookup(top_module);

        if(cmdline.isset("outfile"))
        {
          std::ofstream out(cmdline.get_value("outfile").c_str());
          if(!out)
          {
            error() << "failed to open given outfile" << eom;
            return 6;
          }

          gen_interface(goto_model.symbol_table, symbol, true, out, std::cerr);
        }
        else
          gen_interface(goto_model.symbol_table, symbol, true, std::cout, std::cerr);

        return 0; // done
      }
      
      //
      // map HDL variables to C variables
      //

      status() << "Mapping variables" << eom;

      map_vars(
        goto_model.symbol_table,
        top_module,
        bmc_constraints,
        get_message_handler(),
        get_bound());
    }

    catch(int e) { return 6; }
  }
  else if(cmdline.isset("gen-interface"))
  {
    error() << "must specify top module name for gen-interface" << eom;
    return 6;
  }
  else if(cmdline.isset("show-modules"))
  {
    show_modules(goto_model.symbol_table, ui_message_handler.get_ui());
    return 0; // done
  }
    
  return -1; // continue
}

/*******************************************************************\

Function: hw_cbmc_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void hw_cbmc_parse_optionst::help()
{
  std::cout <<
    "* *  hw-cbmc is protected in part by U.S. patent 7,225,417  * *";

  cbmc_parse_optionst::help();

  std::cout <<
    "hw-cbmc also accepts the following options:\n"
    " --module name                top module for unwinding (deprecated)\n"
    " --top name                   top module for unwinding\n"
    " --bound nr                   number of transitions for the module\n"
    " --gen-interface              print C for interface to module\n"
    " --vcd file                   dump error trace in VCD format\n"
    "\n";
}

