/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <iostream>

#include <util/config.h>
#include <util/get_module.h>

#include <goto-programs/show_claims.h>
#include <goto-programs/set_claims.h>
#include <trans/show_modules.h>
#include <cbmc/version.h>
#include <langapi/mode.h>

#ifdef HAVE_VERILOG
#include <verilog/verilog_language.h>
#endif

#ifdef HAVE_VHDL
#include <vhdl/vhdl_language.h>
#endif

#ifdef HAVE_SMV
#include <smvlang/smv_language.h>
#endif

#include "parseoptions.h"
#include "hw_bmc.h"
#include "map_vars.h"
#include "gen_interface.h"

/*******************************************************************\

Function: hw_cbmc_parseoptionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int hw_cbmc_parseoptionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << std::endl;
    return 0;
  }

  register_languages();

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);

  if(cmdline.isset("vcd"))
    options.set_option("vcd", cmdline.getval("vcd"));

  hw_bmct bmc(options, symbol_table, ui_message_handler);
  set_verbosity(bmc);
  set_verbosity(*this);

  if(cmdline.isset("preprocess"))
  {
    preprocessing();
    return 0;
  }

  goto_functionst goto_functions;

  if(get_goto_program(options, bmc, goto_functions))
    return 6;

  label_claims(goto_functions);

  if(cmdline.isset("show-claims"))
  {
    const namespacet ns(symbol_table);
    show_claims(ns, get_ui(), goto_functions);
    return 0;
  }

  if(set_claims(goto_functions))
    return 7;

  // do actual BMC
  return do_bmc(bmc, goto_functions);
}

/*******************************************************************\

Function: hw_cbmc_parseoptionst::get_modules

  Inputs:

 Outputs:

 Purpose: add additional (synchonous) modules

\*******************************************************************/

bool hw_cbmc_parseoptionst::get_modules(bmct &bmc)
{
  //
  // unwinding of transition systems
  //

  const std::string module=
    cmdline.isset("module")?cmdline.getval("module"):"";

  if(module!="")
  {
    try
    {
      const symbolt &symbol=
        get_module(symbol_table, module, get_message_handler());

      if(cmdline.isset("gen-interface"))
      {
        gen_interface(symbol_table, symbol, true, std::cout, std::cerr);
        return true;
      }
      
      hw_bmct &hw_bmc=dynamic_cast<hw_bmct &>(bmc);

      if(cmdline.isset("bound"))
        hw_bmc.unwind_no_timeframes=atoi(cmdline.getval("bound"))+1;
      else
        hw_bmc.unwind_no_timeframes=1;

      hw_bmc.unwind_module=symbol.name;

      //
      // map HDL variables to C variables
      //

      status("Mapping variables");

      map_vars(
        symbol_table,
        symbol.name,
        hw_bmc.bmc_constraints,
        ui_message_handler,
        hw_bmc.unwind_no_timeframes);
    }

    catch(int e) { return true; }
  }
  else if(cmdline.isset("gen-interface"))
  {
    error("must specify module name for gen-interface");
    return true;
  }
  else if(cmdline.isset("show-modules"))
  {
    show_modules(symbol_table, get_ui());
    return true;
  }
    
  return false;
}

/*******************************************************************\

Function: hw_cbmc_parseoptionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void hw_cbmc_parseoptionst::help()
{
  cbmc_parseoptionst::help();

  std::cout <<
    "hw-cbmc also accepts the following options:\n"
    " --module name                top module for unwinding\n"
    " --bound nr                   number of transitions for the module\n"
    " --gen-interface              print C for interface to module\n"
    " --vcd file                   dump error trace in VCD format\n"
    "\n";
}

/*******************************************************************\

Function: hw_cbmc_parseoptionst::register_languages

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void hw_cbmc_parseoptionst::register_languages()
{
  cbmc_parseoptionst::register_languages();

  #ifdef HAVE_SMV
  register_language(new_smv_language);
  #endif
  
  #ifdef HAVE_VERILOG
  register_language(new_verilog_language);
  #endif
  
  #ifdef HAVE_VHDL
  register_language(new_vhdl_language);
  #endif
}

