/*******************************************************************\

Module: FastPPA Estimation Parse Options

Author: Kiro

\*******************************************************************/

#include "fastppa_parse_options.h"

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/string2int.h>

#include <ebmc/ebmc_error.h>

#include "fastppa_estimator.h"

#include <iostream>

/*******************************************************************\

Function: fastppa_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: parse options and dispatch to estimation engine

\*******************************************************************/

int fastppa_parse_optionst::doit()
{
  if(cmdline.isset("verbosity"))
    ui_message_handler.set_verbosity(
      unsafe_string2unsigned(cmdline.get_value("verbosity")));
  else
    ui_message_handler.set_verbosity(messaget::M_STATUS);

  if(config.set(cmdline))
  {
    usage_error();
    return CPROVER_EXIT_USAGE_ERROR;
  }

  if(cmdline.isset("version"))
  {
    std::cout << "fastppa 0.1\n";
    return 0;
  }

  try
  {
    return run_fastppa_estimation(cmdline, ui_message_handler);
  }
  catch(const ebmc_errort &e)
  {
    if(!e.what().empty())
    {
      messaget message(ui_message_handler);
      message.error() << "error: " << e.what() << messaget::eom;
    }
    return e.exit_code().value_or(CPROVER_EXIT_EXCEPTION);
  }
}

/*******************************************************************\

Function: fastppa_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void fastppa_parse_optionst::help()
{
  std::cout << "\n"
               "fastppa - RTL Cost Estimation\n"
               "\n"
               "Usage:\n"
               " fastppa [options] file.sv\n"
               "\n"
               "Options:\n"
               " --process <name>       target process node (3nm, 7nm, 14nm, "
               "28nm, 45nm, ...)\n"
               " --clock-freq <hz>      target clock frequency in Hz\n"
               " --toggle-rate <alpha>  switching activity (0-1, default 0.1)\n"
               " --netlist              use AIG netlist (more accurate)\n"
               " --top <module>         set top module\n"
               " --verbosity <nr>       verbosity level (0-10)\n"
               " --version              show version\n"
               "\n"
               "Verilog options:\n"
               " -I <path>              set include path\n"
               " -D <var>[=<value>]     set preprocessor define\n"
               " --systemverilog        force SystemVerilog\n"
               "\n"
               "Supported process nodes: 3nm 7nm 14nm 28nm 45nm 65nm 90nm "
               "130nm\n"
               "\n";
}

/*******************************************************************\

Function: fastppa_parse_optionst::register_languages

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fastppa_parse_optionst::register_languages()
{
}
