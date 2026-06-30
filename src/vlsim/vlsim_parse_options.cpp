/*******************************************************************\

Module: vlsim Main Module

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "vlsim_parse_options.h"

#include <util/exit_codes.h>
#include <util/help_formatter.h>
#include <util/string2int.h>

#include <ebmc/ebmc_error.h>
#include <verilog/top_level_modules.h>
#include <verilog/verilog_ebmc_language.h>
#include <verilog/verilog_typecheck.h>

#include "vl_simulator.h"
#include "vlsim_version.h"

#include <iostream>

static int vlsim(const cmdlinet &cmdline, message_handlert &message_handler)
{
  verilog_ebmc_languaget lang(cmdline, message_handler);

  if(cmdline.isset("preprocess"))
  {
    lang.preprocess();
    return 0;
  }

  if(cmdline.isset("show-parse"))
  {
    lang.show_parse();
    return 0;
  }

  // Elaborate: parse + typecheck, without synthesis.
  auto parse_trees = lang.parse();
  auto symbol_table = lang.elaborate_compilation_units(parse_trees);
  auto tops = top_level_modules(parse_trees, cmdline);

  const bool warn_implicit_nets = cmdline.isset("warn-implicit-nets");
  messaget log(message_handler);

  for(const auto &top : tops)
  {
    const auto module_sym = verilog_module_symbol(top);
    log.status() << "Type-checking " << module_sym << messaget::eom;

    if(verilog_typecheck(
         symbol_table,
         module_sym,
         parse_trees.front().standard,
         warn_implicit_nets,
         message_handler))
    {
      log.error() << "CONVERSION ERROR" << messaget::eom;
      throw ebmc_errort{}.with_exit_code(2);
    }
  }

  // Run simulation on each top-level module.
  int result = 0;
  for(const auto &top : tops)
  {
    const auto module_sym = verilog_module_symbol(top);
    vl_simulatort simulator(symbol_table, message_handler);
    int code = simulator.simulate(module_sym);
    if(code != 0)
      result = code;
  }
  return result;
}

/*******************************************************************\

Function: vlsim_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int vlsim_parse_optionst::doit()
{
  if(cmdline.isset("verbosity"))
    ui_message_handler.set_verbosity(
      unsafe_string2unsigned(cmdline.get_value("verbosity")));
  else
    ui_message_handler.set_verbosity(messaget::M_STATUS);

  if(cmdline.isset("version"))
  {
    std::cout << VLSIM_VERSION << '\n';
    return 0;
  }

  try
  {
    return vlsim(cmdline, ui_message_handler);
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

Function: vlsim_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void vlsim_parse_optionst::help()
{
  std::cout
    << "\n"
    << banner_string("VLSIM", VLSIM_VERSION) << '\n'
    << "* *                  Copyright (C) 2025                     * *\n"
       "* *                 dkr@amazon.com                   * *\n"
       "\n";

  std::cout << help_formatter(
    // clang-format off
    "Usage:\tPurpose:\n"
    "\n"
    " {bvlsim} [{y-?}] [{y-h}] [{y--help}] \t show help\n"
    " {bvlsim} {ufile} {u...}      \t source file names\n"
    "\n"
    "Options:\n"
    " {y--top} {uname}               \t set top module\n"
    " {y-I} {upath}                  \t set include path\n"
    " {y-D} {uname}                  \t set preprocessor define\n"
    " {y--systemverilog}             \t force SystemVerilog mode\n"
    " {y--warn-implicit-nets}        \t warn about implicit nets\n"
    " {y--verbosity} {u#}            \t verbosity level\n"
    "\n"
    "Actions:\n"
    " {y--preprocess}                \t output the preprocessed source file\n"
    " {y--show-parse}                \t show the parse tree\n"
    // clang-format on
    "\n");
}
