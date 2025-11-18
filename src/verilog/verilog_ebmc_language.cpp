/*******************************************************************\

Module: Verilog Language Interface

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Verilog Language Interface

#include "verilog_ebmc_language.h"

#include <util/cmdline.h>
#include <util/get_module.h>
#include <util/suffix.h>
#include <util/unicode.h>

#include <ebmc/ebmc_error.h>
#include <ebmc/ebmc_language_file.h>
#include <ebmc/output_file.h>
#include <ebmc/show_modules.h>
#include <ebmc/transition_system.h>
#include <langapi/language_util.h>
#include <trans-word-level/show_module_hierarchy.h>

#include "verilog_language.h"
#include "verilog_parser.h"
#include "verilog_typecheck.h"

#include <fstream>
#include <iostream>

static void
preprocess(const cmdlinet &cmdline, message_handlert &message_handler)
{
  messaget message(message_handler);

  if(cmdline.args.size() != 1)
    throw ebmc_errort{}.with_exit_code(1)
      << "please give exactly one file to preprocess";

  const auto &filename = cmdline.args.front();
  std::ifstream infile(widen_if_needed(filename));

  if(!infile)
    throw ebmc_errort{}.with_exit_code(1)
      << "failed to open input file `" << filename << "'";

  auto language = new_verilog_language();

  optionst options;

  // do -I
  if(cmdline.isset('I'))
    options.set_option("I", cmdline.get_values('I'));

  options.set_option("force-systemverilog", cmdline.isset("systemverilog"));

  // do -D
  if(cmdline.isset('D'))
    options.set_option("defines", cmdline.get_values('D'));

  language->set_language_options(options, message_handler);

  if(language->preprocess(infile, filename, std::cout, message_handler))
    throw ebmc_errort{}.with_exit_code(1);
}

static bool parse(
  const cmdlinet &cmdline,
  const std::string &filename,
  ebmc_language_filest &language_files,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  std::ifstream infile(widen_if_needed(filename));

  if(!infile)
  {
    message.error() << "failed to open input file `" << filename << "'"
                    << messaget::eom;
    return true;
  }

  auto &lf = language_files.add_file(filename);
  lf.filename = filename;
  lf.language = new_verilog_language();
  languaget &language = *lf.language;

  optionst options;

  // do -I
  if(cmdline.isset('I'))
    options.set_option("I", cmdline.get_values('I'));

  options.set_option("force-systemverilog", cmdline.isset("systemverilog"));
  options.set_option("vl2smv-extensions", cmdline.isset("vl2smv-extensions"));
  options.set_option("warn-implicit-nets", cmdline.isset("warn-implicit-nets"));

  // do -D
  if(cmdline.isset('D'))
    options.set_option("defines", cmdline.get_values('D'));

  // do --ignore-initial
  if(cmdline.isset("ignore-initial"))
    options.set_option("ignore-initial", true);

  // do --initial-zero
  if(cmdline.isset("initial-zero"))
    options.set_option("initial-zero", true);

  language.set_language_options(options, message_handler);

  message.status() << "Parsing " << filename << messaget::eom;

  if(language.parse(infile, filename, message_handler))
  {
    message.error() << "PARSING ERROR\n";
    return true;
  }

  lf.get_modules();

  return false;
}

static bool parse(
  const cmdlinet &cmdline,
  ebmc_language_filest &language_files,
  message_handlert &message_handler)
{
  for(auto &arg : cmdline.args)
  {
    if(parse(cmdline, arg, language_files, message_handler))
      return true;
  }
  return false;
}

static bool get_main(
  const cmdlinet &cmdline,
  message_handlert &message_handler,
  transition_systemt &transition_system)
{
  std::string top_module;

  if(cmdline.isset("module"))
    top_module = cmdline.get_value("module");
  else if(cmdline.isset("top"))
    top_module = cmdline.get_value("top");

  try
  {
    transition_system.main_symbol =
      &get_module(transition_system.symbol_table, top_module, message_handler);
    transition_system.trans_expr =
      to_trans_expr(transition_system.main_symbol->value);
  }

  catch(int e)
  {
    return true;
  }

  return false;
}

static void make_next_state(exprt &expr)
{
  for(auto &sub_expression : expr.operands())
    make_next_state(sub_expression);

  if(expr.id() == ID_symbol)
    expr.id(ID_next_symbol);
}

std::optional<transition_systemt> verilog_ebmc_languaget::transition_system()
{
  messaget message(message_handler);

  //
  // preprocessing
  //
  if(cmdline.isset("preprocess"))
  {
    preprocess(cmdline, message_handler);
    return {};
  }

  //
  // parsing
  //
  ebmc_language_filest language_files;

  if(parse(cmdline, language_files, message_handler))
    throw ebmc_errort{}.with_exit_code(1);

  if(cmdline.isset("show-parse"))
  {
    language_files.show_parse(std::cout, message_handler);
    return {};
  }

  //
  // type checking
  //

  message.status() << "Converting" << messaget::eom;

  transition_systemt transition_system;

  if(language_files.typecheck(transition_system.symbol_table, message_handler))
  {
    message.error() << "CONVERSION ERROR" << messaget::eom;
    throw ebmc_errort{}.with_exit_code(2);
  }

  if(cmdline.isset("show-modules"))
  {
    show_modulest::from_symbol_table(transition_system.symbol_table)
      .plain_text(std::cout);
    return {};
  }

  if(cmdline.isset("modules-xml"))
  {
    auto filename = cmdline.get_value("modules-xml");
    auto out_file = output_filet{filename};
    show_modulest::from_symbol_table(transition_system.symbol_table)
      .xml(out_file.stream());
    return {};
  }

  if(cmdline.isset("json-modules"))
  {
    auto out_file = output_filet{cmdline.get_value("json-modules")};
    show_modulest::from_symbol_table(transition_system.symbol_table)
      .json(out_file.stream());
    return {};
  }

  if(cmdline.isset("show-symbol-table"))
  {
    std::cout << transition_system.symbol_table;
    return {};
  }

  // get module name

  if(get_main(cmdline, message_handler, transition_system))
    throw ebmc_errort{}.with_exit_code(1);

  if(cmdline.isset("show-module-hierarchy"))
  {
    DATA_INVARIANT(
      transition_system.main_symbol != nullptr, "must have main_symbol");
    show_module_hierarchy(
      transition_system.symbol_table,
      *transition_system.main_symbol,
      std::cout);
    return {};
  }

  // --reset given?
  if(cmdline.isset("reset"))
  {
    namespacet ns(transition_system.symbol_table);
    exprt reset_constraint = to_expr(
      ns, transition_system.main_symbol->name, cmdline.get_value("reset"));

    // true in initial state
    transt new_trans_expr = transition_system.trans_expr;
    new_trans_expr.init() = and_exprt(new_trans_expr.init(), reset_constraint);

    // and not anymore afterwards
    exprt reset_next_state = reset_constraint;
    make_next_state(reset_next_state);

    new_trans_expr.trans() =
      and_exprt(new_trans_expr.trans(), not_exprt(reset_next_state));
    transition_system.trans_expr = new_trans_expr;
  }

  // done with the transition system
  return transition_system;
}
