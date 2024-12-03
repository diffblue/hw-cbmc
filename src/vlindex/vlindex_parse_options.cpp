/*******************************************************************\

Module: vlindex Main Module

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "vlindex_parse_options.h"

#include <util/exit_codes.h>
#include <util/help_formatter.h>
#include <util/string2int.h>

#include <ebmc/ebmc_error.h>

#include "verilog_indexer.h"

#include <iostream>

/*******************************************************************\

Function: vlindex_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int vlindex_parse_optionst::doit()
{
  if(cmdline.isset("verbosity"))
    ui_message_handler.set_verbosity(
      unsafe_string2unsigned(cmdline.get_value("verbosity")));
  else
    ui_message_handler.set_verbosity(messaget::M_STATUS); // default

  if(cmdline.isset("version"))
  {
    std::cout << EBMC_VERSION << '\n';
    return 0;
  }

  try
  {
    return verilog_index(cmdline);
  }
  catch(const ebmc_errort &ebmc_error)
  {
    if(!ebmc_error.what().empty())
    {
      messaget message(ui_message_handler);
      if(ebmc_error.location().is_not_nil())
        message.error().source_location = ebmc_error.location();

      message.error() << "error: " << messaget::red << ebmc_error.what()
                      << messaget::reset << messaget::eom;
    }
    return ebmc_error.exit_code().value_or(CPROVER_EXIT_EXCEPTION);
  }
}

/*******************************************************************\

Function: vlindex_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void vlindex_parse_optionst::help()
{
  std::cout
    << "\n"
       "* *             VLINDEX - Copyright (C) 2024                * *\n"
       "* *                     Version " EBMC_VERSION
       "                         * *\n"
       "* *                    dkr@amazon.com                       * *\n"
       "\n";

  std::cout << help_formatter(
    // clang-format off
    "Usage:\tPurpose:\n"
    "\n"
    " {bvlindex} [{y-?}] [{y-h}] [{y--help}] \t show help\n"
    " {bvlindex} {ufile} {u...}      \t source file names\n"
    "\n"
    "Additonal options:\n"
    " {y--top} {umodule}             \t set top module\n"
    " {y-I} {upath}                  \t set include path\n"
    " {y--1800-2017}                 \t recognize 1800-2017 SystemVerilog (default)\n"
    " {y--1800-2012}                 \t recognize 1800-2012 SystemVerilog\n"
    " {y--1800-2009}                 \t recognize 1800-2009 SystemVerilog\n"
    " {y--1800-2005}                 \t recognize 1800-2005 SystemVerilog\n"
    " {y--1364-2005}                 \t recognize 1364-2005 Verilog\n"
    " {y--1364-2001}                 \t recognize 1364-2001 Verilog\n"
    " {y--1364-2001-noconfig}        \t recognize 1364-2001-noconfig Verilog\n"
    " {y--1364-1995}                 \t recognize 1364-1995 Verilog\n"
    "\n"
    "Actions:\n"
    " {y--preprocess}                \t output the preprocessed source file\n"
    " {y--modules}                   \t show a list of the modules\n"
    " {y--instances}                 \t show a list of the module instances\n"
    " {y--classes}                   \t show a list of the module classes\n"
    " {y--packages}                  \t show a list of the module packages\n"
    " {y--udps}                      \t show a list of the UPDs\n"
    " {y--tasks}                     \t show a list of the tasks\n"
    " {y--functions}                 \t show a list of the functions\n"
    " {y--properties}                \t show a list of the properties\n"
    " {y--sequences}                 \t show a list of the sequences\n"
    " {y--hierarchy}                 \t show the hierarchy of module instantiations\n"
    " {y--verbosity} {u#}            \t verbosity level, from 0 (silent) to 10 (everything)\n"
    // clang-format on
    "\n");
}
