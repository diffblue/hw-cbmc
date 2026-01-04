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
#include <functional>
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

static void module_dependencies_rec(
  const verilog_module_itemt &module_item,
  const std::function<void(irep_idt)> &action)
{
  if(module_item.id() == ID_inst)
  {
    action(to_verilog_inst(module_item).get_module());
  }
  else if(module_item.id() == ID_generate_block)
  {
    for(auto &sub_item : to_verilog_generate_block(module_item).module_items())
      module_dependencies_rec(sub_item, action);
  }
  else if(module_item.id() == ID_generate_if)
  {
    auto &generate_if = to_verilog_generate_if(module_item);
    module_dependencies_rec(generate_if.then_case(), action);
    if(generate_if.has_else_case())
      module_dependencies_rec(generate_if.else_case(), action);
  }
  else if(module_item.id() == ID_generate_for)
  {
    module_dependencies_rec(
      to_verilog_generate_for(module_item).body(), action);
  }
}

static void module_dependencies(
  const verilog_module_sourcet &module_source,
  const std::function<void(irep_idt)> &action)
{
  for(auto &item : module_source.items())
    module_dependencies_rec(item, action);
}

irep_idt
verilog_ebmc_languaget::top_level_module(const parse_treest &parse_trees) const
{
  // start with a set of all modules, from all the files
  std::set<irep_idt> all_modules;

  for(auto &parse_tree : parse_trees)
    for(auto &item : parse_tree.items)
    {
      if(item.id() == ID_verilog_module)
      {
        auto base_name = to_verilog_module_source(item).base_name();
        all_modules.insert(base_name);
      }
    }

  // Did the user specify one?
  irep_idt given_module;

  if(cmdline.isset("module"))
    given_module = cmdline.get_value("module");
  else if(cmdline.isset("top"))
    given_module = cmdline.get_value("top");

  if(given_module != irep_idt{})
  {
    if(all_modules.find(given_module) == all_modules.end())
    {
      messaget log{message_handler};
      log.error() << "module '" << given_module << "' not found"
                  << messaget::eom;
      throw ebmc_errort{}.with_exit_code(2);
    }
    else
      return given_module; // done
  }

  // start with all modules, and then erase the ones that are
  // used as a dependency
  std::set<irep_idt> top_level_modules = all_modules;

  for(auto &parse_tree : parse_trees)
  {
    for(auto &item : parse_tree.items)
    {
      if(item.id() == ID_verilog_module || item.id() == ID_verilog_program)
      {
        auto erase = [&top_level_modules](irep_idt dependency)
        { top_level_modules.erase(dependency); };
        module_dependencies(to_verilog_module_source(item), erase);
      }
    }
  }

  if(top_level_modules.empty())
  {
    messaget log{message_handler};
    log.error() << "no module found" << messaget::eom;
    throw ebmc_errort{}.with_exit_code(1);
  }
  else if(top_level_modules.size() >= 2)
  {
    // sorted alphabetically
    std::set<std::string> modules;

    for(const auto &base_name : top_level_modules)
      modules.insert(id2string(base_name));

    messaget log{message_handler};
    log.error() << "multiple modules found, please select one:\n";

    for(const auto &module : modules)
      log.error() << "  " << module << '\n';

    log.error() << messaget::eom;
    throw ebmc_errort{}.with_exit_code(1);
  }

  // we have exactly one top-level module
  return *top_level_modules.begin();
}

static bool get_main(
  irep_idt top_level_module,
  message_handlert &message_handler,
  transition_systemt &transition_system)
{
  try
  {
    auto identifier = verilog_module_symbol(top_level_module);
    auto symbol_it = transition_system.symbol_table.symbols.find(identifier);
    CHECK_RETURN(symbol_it != transition_system.symbol_table.symbols.end());
    transition_system.main_symbol = &symbol_it->second;
    transition_system.trans_expr = to_trans_expr(symbol_it->second.value);
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

/// extract the list of modules from the Verilog parse trees
static show_modulest
show_modules(const verilog_ebmc_languaget::parse_treest &parse_trees)
{
  show_modulest result;

  irep_idt mode = ID_Verilog;

  for(auto &parse_tree : parse_trees)
  {
    for(const auto &item : parse_tree.items)
    {
      if(item.id() == ID_verilog_module || item.id() == ID_verilog_checker)
      {
        auto &verilog_module = to_verilog_module_source(item);
        auto base_name = verilog_module.base_name();
        auto identifier = verilog_module_symbol(base_name);
        result.modules.emplace_back(
          identifier, base_name, mode, verilog_module.source_location());
      }
    }
  }

  return result;
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

  if(cmdline.isset("show-modules"))
  {
    show_modules(parse_trees).plain_text(std::cout);
    return {};
  }

  if(cmdline.isset("modules-xml"))
  {
    auto filename = cmdline.get_value("modules-xml");
    auto out_file = output_filet{filename};
    show_modules(parse_trees).xml(out_file.stream());
    return {};
  }

  if(cmdline.isset("json-modules"))
  {
    auto out_file = output_filet{cmdline.get_value("json-modules")};
    show_modules(parse_trees).json(out_file.stream());
    return {};
  }

  //
  // type checking
  //

  message.status() << "Converting" << messaget::eom;

  auto transition_system = typecheck(parse_trees);

  if(cmdline.isset("show-symbol-table"))
  {
    std::cout << transition_system.symbol_table;
    return {};
  }

  //
  // determine the top-level module
  //
  auto top_level_module = this->top_level_module(parse_trees);

  if(get_main(top_level_module, message_handler, transition_system))
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
