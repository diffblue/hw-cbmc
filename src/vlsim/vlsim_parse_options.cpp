/*******************************************************************\

Module: vlsim Main Module

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "vlsim_parse_options.h"

#include <util/exit_codes.h>
#include <util/help_formatter.h>
#include <util/string2int.h>

#include <ebmc/ebmc_error.h>
#include <ebmc/ebmc_version.h>
#include <ebmc/transition_system.h>

#include <verilog/verilog_ebmc_language.h>
#include <verilog/verilog_typecheck.h>
#include <verilog/verilog_typecheck_base.h>

#include "vl_simulator.h"

#include <iostream>
#include <map>
#include <set>
#include <string>

/*******************************************************************\

   Class: vlsim_languaget

  Inputs:

 Outputs:

 Purpose: Verilog language interface for vlsim.
          Elaborates (parses and typechecks) without synthesis.

\*******************************************************************/

class vlsim_languaget : public verilog_ebmc_languaget
{
public:
  vlsim_languaget(
    const cmdlinet &_cmdline,
    message_handlert &_message_handler)
    : verilog_ebmc_languaget(_cmdline, _message_handler)
  {
  }

  // Overrides the base class to implement vlsim-specific modes.
  // For the default (elaboration) mode, we parse and typecheck
  // without synthesis.
  std::optional<transition_systemt> transition_system() override;

  /// Run simulation on all top-level modules.
  /// Returns an exit code: 0 for success, non-zero for failure.
  int simulate();

private:
  // Set after transition_system() completes successfully.
  symbol_tablet symbol_table_;
  std::vector<irep_idt> tops_;
};

std::optional<transition_systemt> vlsim_languaget::transition_system()
{
  if(cmdline.isset("preprocess"))
  {
    preprocess();
    return {};
  }

  if(cmdline.isset("show-parse"))
  {
    show_parse();
    return {};
  }

  // Elaborate: parse + typecheck, without synthesis.

  auto parse_trees = parse();
  symbol_table_ = elaborate_compilation_units(parse_trees);
  tops_ = top_level_modules(parse_trees);

  // Build a map from module symbol to parse tree
  std::map<std::string, const parse_treet *> module_to_tree;
  for(const auto &parse_tree : parse_trees)
  {
    std::set<std::string> module_ids;
    parse_tree.modules_provided(module_ids);
    for(const auto &id : module_ids)
      module_to_tree[id] = &parse_tree;
  }

  const bool warn_implicit_nets = cmdline.isset("warn-implicit-nets");
  messaget log(message_handler);

  for(const auto &top : tops_)
  {
    const auto module_sym = verilog_module_symbol(top);
    log.status() << "Type-checking " << module_sym << messaget::eom;

    const auto it = module_to_tree.find(id2string(module_sym));
    if(it == module_to_tree.end())
    {
      throw ebmc_errort{}.with_exit_code(1)
        << "module not found: " << module_sym;
    }

    if(verilog_typecheck(
         symbol_table_,
         module_sym,
         it->second->standard,
         warn_implicit_nets,
         message_handler))
    {
      log.error() << "CONVERSION ERROR" << messaget::eom;
      throw ebmc_errort{}.with_exit_code(2);
    }
  }

  return {};
}

int vlsim_languaget::simulate()
{
  // Run simulation on each top-level module.
  // Return the exit code from the last module simulated,
  // or 0 if all succeeded.
  int result = 0;
  for(const auto &top : tops_)
  {
    const auto module_sym = verilog_module_symbol(top);
    vl_simulatort simulator(symbol_table_, message_handler);
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
    std::cout << EBMC_VERSION << '\n';
    return 0;
  }

  try
  {
    vlsim_languaget lang(cmdline, ui_message_handler);
    lang.transition_system();
    return lang.simulate();
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
    << banner_string("VLSIM", EBMC_VERSION) << '\n'
    << "* *                  Copyright (C) 2025                     * *\n"
       "* *                 kroening@kroening.com                   * *\n"
       "\n";

  std::cout << help_formatter(
    // clang-format off
    "Usage:\tPurpose:\n"
    "\n"
    " {bvlsim} [{y-?}] [{y-h}] [{y--help}] \t show help\n"
    " {bvlsim} {ufile} {u...}      \t source file names\n"
    "\n"
    "Options:\n"
    " {y--module} {uname}            \t set top module\n"
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
