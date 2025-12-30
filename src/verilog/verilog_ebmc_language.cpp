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
#include <ebmc/output_file.h>
#include <ebmc/show_modules.h>
#include <ebmc/transition_system.h>
#include <langapi/language_util.h>
#include <trans-word-level/show_module_hierarchy.h>

#include "verilog_language.h"
#include "verilog_parser.h"
#include "verilog_preprocessor.h"
#include "verilog_synthesis.h"
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

verilog_ebmc_languaget::parse_treest verilog_ebmc_languaget::parse()
{
  parse_treest parse_trees;

  for(auto &arg : cmdline.args)
    parse_trees.push_back(parse(arg));

  return parse_trees;
}

void verilog_ebmc_languaget::typecheck_module(
  modulet &module,
  symbol_tablet &symbol_table)
{
  // already typechecked?
  if(module.type_checked)
    return;

  messaget log(message_handler);

  // already in progress?

  if(module.in_progress)
    throw ebmc_errort{} << "circular dependency in " << module.identifier;

  module.in_progress = true;

  // first get dependencies of current module
  const auto dependency_set = module.parse_tree.dependencies(module.identifier);

  // type check the dependencies
  for(auto &dependency : dependency_set)
  {
    // look it up
    auto dependency_it = module_map.find(dependency);

    // might not exist
    if(dependency_it == module_map.end())
    {
      log.error() << "found no file that provides module " << dependency
                  << messaget::eom;
      throw ebmc_errort{}.with_exit_code(2);
    }

    typecheck_module(dependency_it->second, symbol_table);
  }

  // type check the module
  log.status() << "Type-checking " << module.identifier << messaget::eom;

  const bool warn_implicit_nets = cmdline.isset("warn-implicit-nets");

  if(verilog_typecheck(
       module.parse_tree,
       symbol_table,
       module.identifier,
       warn_implicit_nets,
       message_handler))
  {
    log.error() << "CONVERSION ERROR" << messaget::eom;
    throw ebmc_errort{}.with_exit_code(2);
  }

  messaget message(message_handler);
  log.status() << "Synthesis " << module.identifier << messaget::eom;

  const bool ignore_initial = cmdline.isset("ignore-initial");
  const bool initial_zero = cmdline.isset("initial-zero");

  if(verilog_synthesis(
       symbol_table,
       module.identifier,
       module.parse_tree.standard,
       ignore_initial,
       initial_zero,
       message_handler))
  {
    log.error() << "CONVERSION ERROR" << messaget::eom;
    throw ebmc_errort{}.with_exit_code(2);
  }

  module.type_checked = true;
  module.in_progress = false;
}

transition_systemt
verilog_ebmc_languaget::typecheck(const parse_treest &parse_trees)
{
  // set up the module map
  for(auto &parse_tree : parse_trees)
  {
    std::set<std::string> module_identifiers;
    parse_tree.modules_provided(module_identifiers);

    for(auto &module_identifier : module_identifiers)
    {
      auto identifier = module_identifier;
      module_map.emplace(identifier, modulet{module_identifier, parse_tree});
    }
  }

  // now type check
  transition_systemt transition_system;

  for(auto &[_, module] : module_map)
  {
    typecheck_module(module, transition_system.symbol_table);
  }

  return transition_system;
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

  auto parse_trees = parse();

  //
  // type checking
  //

  message.status() << "Converting" << messaget::eom;

  auto transition_system = typecheck(parse_trees);

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
