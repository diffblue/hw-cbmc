/*******************************************************************\

Module: Verilog Language Interface

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Verilog Language Interface

#include "verilog_ebmc_language.h"

#include <util/cmdline.h>
#include <util/get_module.h>
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
#include "verilog_preprocessor.h"
#include "verilog_typecheck.h"

#include <fstream>
#include <iostream>

void verilog_ebmc_languaget::preprocess(
  const std::filesystem::path &path,
  std::ostream &out)
{
  std::ifstream infile{path};

  if(!infile)
    throw ebmc_errort{}.with_exit_code(1)
      << "failed to open input file " << path;

  // do -I and -D
  auto &include_paths = cmdline.get_values('I');
  auto &initial_defines = cmdline.get_values('D');

  verilog_preprocessort preprocessor(
    infile,
    out,
    message_handler,
    path.u8string(),
    include_paths,
    initial_defines);

  try
  {
    preprocessor.preprocessor();
  }
  catch(int e)
  {
    throw ebmc_errort{}.with_exit_code(1);
  }
}

void verilog_ebmc_languaget::preprocess()
{
  if(cmdline.args.size() != 1)
    throw ebmc_errort{}.with_exit_code(1)
      << "please give exactly one file to preprocess";

  const auto file_name = widen_if_needed(cmdline.args.front());

  preprocess(file_name, std::cout);
}

void verilog_ebmc_languaget::parse(
  const std::filesystem::path &path,
  ebmc_language_filest &language_files)
{
  messaget message(message_handler);

  message.status() << "Parsing " << path << messaget::eom;

  auto verilog_language = std::make_unique<verilog_languaget>();
  verilog_language->get_parse_tree() = parse(path);

  optionst options;

  options.set_option("force-systemverilog", cmdline.isset("systemverilog"));
  options.set_option("vl2smv-extensions", cmdline.isset("vl2smv-extensions"));
  options.set_option("warn-implicit-nets", cmdline.isset("warn-implicit-nets"));

  // do --ignore-initial
  if(cmdline.isset("ignore-initial"))
    options.set_option("ignore-initial", true);

  // do --initial-zero
  if(cmdline.isset("initial-zero"))
    options.set_option("initial-zero", true);

  verilog_language->set_language_options(options, message_handler);

  auto &lf = language_files.add_file(path.u8string());
  lf.filename = path.u8string();
  lf.language = std::unique_ptr<languaget>{std::move(verilog_language)};
  lf.get_modules();
}

verilog_parse_treet
verilog_ebmc_languaget::parse(const std::filesystem::path &path)
{
  verilog_standardt standard;

  if(path.extension() == ".sv" || cmdline.isset("systemverilog"))
    standard = verilog_standardt::SV2023;
  else if(cmdline.isset("vl2smv-extensions"))
    standard = verilog_standardt::V2005_SMV;
  else
    standard = verilog_standardt::V2005_SMV;

  std::stringstream preprocessed;
  preprocess(path, preprocessed);

  verilog_parsert verilog_parser{standard, message_handler};

  verilog_parser.set_file(path.u8string());
  verilog_parser.in = &preprocessed;
  verilog_parser.grammar = verilog_parsert::LANGUAGE;

  verilog_scanner_init();

  if(verilog_parser.parse())
    throw ebmc_errort{}.with_exit_code(1);

  verilog_parser.parse_tree.build_item_map();

  return std::move(verilog_parser.parse_tree);
}

void verilog_ebmc_languaget::show_parse(const std::filesystem::path &path)
{
  messaget message{message_handler};

  message.status() << "Parsing " << path << messaget::eom;

  auto parse_tree = parse(path);

  parse_tree.show(std::cout);
}

void verilog_ebmc_languaget::show_parse()
{
  for(auto &arg : cmdline.args)
    show_parse(widen_if_needed(arg));
}

void verilog_ebmc_languaget::parse(ebmc_language_filest &language_files)
{
  for(auto &arg : cmdline.args)
    parse(arg, language_files);
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
    preprocess();
    return {};
  }

  //
  // parsing
  //
  if(cmdline.isset("show-parse"))
  {
    show_parse();
    return {};
  }

  ebmc_language_filest language_files;
  parse(language_files);

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
