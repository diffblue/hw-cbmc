/*******************************************************************\

Module: Verilog Language Interface

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Verilog Language Interface

#include "verilog_ebmc_language.h"

#include <util/cmdline.h>
#include <util/get_module.h>
#include <util/output_file.h>
#include <util/unicode.h>

#include <ebmc/ebmc_error.h>
#include <ebmc/show_modules.h>
#include <ebmc/transition_system.h>
#include <langapi/language_util.h>
#include <trans-word-level/show_module_hierarchy.h>

#include "verilog_elaborate_compilation_unit.h"
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

verilog_parse_treet verilog_ebmc_languaget::parse(
  const std::filesystem::path &path,
  verilog_scopest &scopes)
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

  verilog_parsert verilog_parser{standard, scopes, message_handler};

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

  verilog_scopest scopes;
  auto parse_tree = parse(path, scopes);

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
  verilog_scopest scopes;

  for(auto &arg : cmdline.args)
    parse_trees.push_back(parse(arg, scopes));

  return parse_trees;
}

void verilog_ebmc_languaget::typecheck_module(
  modulet &module,
  symbol_tablet &symbol_table)
{
  messaget log(message_handler);

  // type check the module
  log.status() << "Type-checking " << module.identifier << messaget::eom;

  const bool warn_implicit_nets = cmdline.isset("warn-implicit-nets");

  if(verilog_typecheck(
       symbol_table,
       module.identifier,
       module.parse_tree.standard,
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
}

transition_systemt verilog_ebmc_languaget::typecheck(
  const parse_treest &parse_trees,
  const std::vector<irep_idt> top_level_modules,
  symbol_tablet &&symbol_table)
{
  std::map<irep_idt, modulet> module_map;

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

  // now type check the given top-level modules
  transition_systemt transition_system;
  transition_system.symbol_table = std::move(symbol_table);

  for(auto top_level_module : top_level_modules)
  {
    auto m_it = module_map.find(verilog_module_symbol(top_level_module));
    CHECK_RETURN(m_it != module_map.end());

    typecheck_module(m_it->second, transition_system.symbol_table);
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

/// Determine the set of top-level modules following 1800 2017 23.3.1,
/// given via their base names. Sorted alphabetically.
std::vector<irep_idt>
verilog_ebmc_languaget::top_level_modules(const parse_treest &parse_trees) const
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

  // Did the user specify a set of top level modules?
  std::vector<irep_idt> given_modules;

  if(cmdline.isset("module"))
  {
    for(auto &value : cmdline.get_values("module"))
      given_modules.push_back(value);
  }
  else if(cmdline.isset("top"))
  {
    for(auto &value : cmdline.get_values("top"))
      given_modules.push_back(value);
  }

  if(!given_modules.empty())
  {
    // first check that all the given modules exist
    for(const auto &given_module : given_modules)
    {
      if(all_modules.find(given_module) == all_modules.end())
      {
        messaget log{message_handler};
        log.error() << "module '" << given_module << "' not found"
                    << messaget::eom;
        throw ebmc_errort{}.with_exit_code(2);
      }
    }

    // now sort alphabetically
    std::sort(
      given_modules.begin(),
      given_modules.end(),
      [](const irep_idt &a, const irep_idt &b)
      { return id2string(a) < id2string(b); });

    return given_modules; // done
  }

  // No modules given. Find all modules that are not used
  // as a submodule. Start with all modules, and then erase
  // the ones that are used as a submodule.
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

  // sort alphabetically into a vector
  std::vector<irep_idt> result;

  for(auto &module : top_level_modules)
    result.push_back(module);

  std::sort(
    result.begin(),
    result.end(),
    [](const irep_idt &a, const irep_idt &b)
    { return id2string(a) < id2string(b); });

  return result; // done
}

static bool get_main(
  const std::vector<irep_idt> top_level_modules,
  message_handlert &message_handler,
  transition_systemt &transition_system)
{
  if(top_level_modules.size() >= 2)
  {
    messaget log{message_handler};
    log.error() << "multiple modules found, please select one:\n";

    for(const auto &module : top_level_modules)
      log.error() << "  " << module << '\n';

    log.error() << messaget::eom;
    throw ebmc_errort{}.with_exit_code(1);
  }

  auto top_level_module = top_level_modules.front();

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

symbol_tablet verilog_ebmc_languaget::elaborate_compilation_units(
  const parse_treest &parse_trees)
{
  symbol_tablet symbol_table;

  const bool warn_implicit_nets = cmdline.isset("warn-implicit-nets");

  for(auto &parse_tree : parse_trees)
    verilog_elaborate_compilation_unit(
      parse_tree, warn_implicit_nets, symbol_table, message_handler);

  return symbol_table;
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
  // copy the parse trees into the symbol table
  //
  symbol_tablet symbol_table = elaborate_compilation_units(parse_trees);

  //
  // determine the top-level modules
  //
  auto top_level_modules = this->top_level_modules(parse_trees);

  //
  // type checking
  //

  message.status() << "Converting" << messaget::eom;

  auto transition_system =
    typecheck(parse_trees, top_level_modules, std::move(symbol_table));

  if(cmdline.isset("show-symbol-table"))
  {
    std::cout << transition_system.symbol_table;
    return {};
  }

  if(get_main(top_level_modules, message_handler, transition_system))
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
