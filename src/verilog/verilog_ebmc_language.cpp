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
#include <langapi/mode.h>
#include <trans-word-level/show_module_hierarchy.h>

#include "top_level_modules.h"
#include "verilog_elaborate_compilation_unit.h"
#include "verilog_language.h"
#include "verilog_lowering.h"
#include "verilog_parse_order.h"
#include "verilog_parser.h"
#include "verilog_preprocessor.h"
#include "verilog_synthesis.h"
#include "verilog_typecheck.h"
#include "verilog_types.h"

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

  // -D
  auto &d_list = cmdline.get_values('D');
  auto &define_list = cmdline.get_values("define");

  // Merge -D defines with +define+ defines
  std::list<std::string> initial_defines;
  initial_defines.insert(initial_defines.end(), d_list.begin(), d_list.end());
  initial_defines.insert(
    initial_defines.end(), define_list.begin(), define_list.end());

  // -I
  auto &I_paths = cmdline.get_values('I');
  auto &incdir_paths = cmdline.get_values("incdir");

  // Collect +incdir+ paths and merge with -I paths
  std::list<std::string> all_include_paths;
  all_include_paths.insert(
    all_include_paths.end(), I_paths.begin(), I_paths.end());
  all_include_paths.insert(
    all_include_paths.end(), incdir_paths.begin(), incdir_paths.end());

  verilog_preprocessort preprocessor(
    infile,
    out,
    message_handler,
    path.u8string(),
    all_include_paths,
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

verilog_standardt
verilog_ebmc_languaget::standard(const std::filesystem::path &path) const
{
  if(path.extension() == ".sv" || cmdline.isset("systemverilog"))
    return verilog_standardt::SV2023;
  else if(cmdline.isset("vl2smv-extensions"))
    return verilog_standardt::V2005_SMV;
  else
    return verilog_standardt::V2005_SMV;
}

verilog_parse_treet verilog_ebmc_languaget::parse(
  const std::filesystem::path &path,
  std::istream &preprocessed,
  verilog_scopest &scopes)
{
  verilog_parsert verilog_parser{standard(path), scopes, message_handler};

  verilog_parser.set_file(path.u8string());
  verilog_parser.in = &preprocessed;
  verilog_parser.grammar = verilog_parsert::LANGUAGE;

  verilog_scanner_init();

  if(verilog_parser.parse())
    throw ebmc_errort{}.with_exit_code(1);

  verilog_parser.parse_tree.build_item_map();

  return std::move(verilog_parser.parse_tree);
}

verilog_parse_treet verilog_ebmc_languaget::parse(
  const std::filesystem::path &path,
  verilog_scopest &scopes)
{
  std::stringstream preprocessed;
  preprocess(path, preprocessed);

  return parse(path, preprocessed, scopes);
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
  // The input files, in the order in which they were given.
  std::vector<std::filesystem::path> paths;

  for(auto &arg : cmdline.args)
    paths.push_back(widen_if_needed(arg));

  // Library files specified with -l and +libfile+
  for(auto &lib_file : cmdline.get_values('l'))
    paths.push_back(widen_if_needed(lib_file));

  for(auto &lib_file : cmdline.get_values("libfile"))
    paths.push_back(widen_if_needed(lib_file));

  // Preprocess the input files, in the order in which they were given.
  // We keep the results, as each of them is read twice below.
  std::vector<std::stringstream> preprocessed(paths.size());

  for(std::size_t i = 0; i < paths.size(); i++)
    preprocess(paths[i], preprocessed[i]);

  // IEEE 1800-2017 26.3 requires that a package is compiled before the
  // scopes that import it, but the order of the input files is not
  // prescribed. We hence determine the order in which to parse the files
  // from the packages that they declare and reference.
  std::vector<verilog_package_usaget> usage;
  usage.reserve(paths.size());

  for(std::size_t i = 0; i < paths.size(); i++)
  {
    usage.push_back(
      verilog_scan_package_usage(preprocessed[i], standard(paths[i])));

    // rewind, for the parser
    preprocessed[i].clear();
    preprocessed[i].seekg(0);
  }

  // Now parse, in dependency order, using one scope table for all files.
  std::vector<std::optional<parse_treet>> results(paths.size());
  verilog_scopest scopes;

  elaboration_order = verilog_parse_order(usage);

  for(auto i : elaboration_order)
    results[i] = parse(paths[i], preprocessed[i], scopes);

  // The parse trees are returned in the order in which the files were
  // given, which is what determines the top-level modules.
  parse_treest parse_trees;

  for(auto &result : results)
  {
    CHECK_RETURN(result.has_value());
    parse_trees.push_back(std::move(*result));
  }

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

  try
  {
    verilog_synthesis(
      symbol_table,
      module.identifier,
      module.parse_tree.standard,
      ignore_initial,
      initial_zero,
      message_handler);
  }
  catch(ebmc_errort)
  {
    log.error() << "CONVERSION ERROR" << messaget::eom;
    throw ebmc_errort{}.with_exit_code(2);
  }
}

transition_systemt verilog_ebmc_languaget::typecheck(
  const parse_treest &parse_trees,
  const std::vector<irep_idt> &top_level_modules,
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

  // set up the transition system
  transition_systemt transition_system;
  transition_system.symbol_table = std::move(symbol_table);

  // Create module instance symbols for the top-level modules under $root,
  // so that $root.module hierarchical identifiers can be resolved
  // while type checking.
  auto root_identifier = verilog_module_symbol(verilog_root_module_name());

  for(auto &top_level_module : top_level_modules)
  {
    auto module_identifier = verilog_module_symbol(top_level_module);

    auto instance_identifier =
      id2string(root_identifier) + "." + id2string(top_level_module);

    symbolt instance_symbol{
      instance_identifier, verilog_module_instance_typet{}, ID_Verilog};
    instance_symbol.base_name = top_level_module;
    instance_symbol.pretty_name = top_level_module;
    instance_symbol.module = root_identifier;
    instance_symbol.value = verilog_module_instancet{module_identifier};

    auto add_result_instance =
      transition_system.symbol_table.add(instance_symbol);
    CHECK_RETURN(!add_result_instance);
  }

  // now type check the top-level modules
  for(auto &top_level_module : top_level_modules)
  {
    auto m_it = module_map.find(verilog_module_symbol(top_level_module));
    CHECK_RETURN(m_it != module_map.end());

    typecheck_module(m_it->second, transition_system.symbol_table);
  }

  return transition_system;
}

/// Create a $root module instance containing the given top-level module,
/// and synthesize it so that the top-level module is expanded into $root.
void verilog_ebmc_languaget::create_root_module(
  const std::vector<irep_idt> &top_level_modules,
  verilog_standardt standard,
  transition_systemt &transition_system)
{
  auto &symbol_table = transition_system.symbol_table;

  auto root_identifier = verilog_module_symbol(verilog_root_module_name());
  verilog_module_exprt::module_itemst root_items;

  for(auto top_level_module : top_level_modules)
  {
    auto module_identifier = verilog_module_symbol(top_level_module);

    // The module instance symbol for the top-level module
    // was already added before type checking.
    auto instance_identifier =
      id2string(root_identifier) + "." + id2string(top_level_module);

    // Build a verilog_instt module item for the instantiation
    verilog_instt inst;
    inst.module_base_name(top_level_module);
    verilog_inst_baset::instancet instance_expr;
    instance_expr.base_name(top_level_module);
    instance_expr.identifier(instance_identifier);
    instance_expr.module_identifier(module_identifier);
    inst.instances().push_back(std::move(instance_expr));

    root_items.push_back(std::move(inst));
  }

  // Create the $root module symbol with the inst items

  symbolt root_symbol{root_identifier, module_typet{}, ID_Verilog};
  root_symbol.base_name = verilog_root_module_name();
  root_symbol.pretty_name = verilog_root_module_name();
  root_symbol.module = root_identifier;
  root_symbol.value = verilog_module_exprt({std::move(root_items)});

  // Create the ports for the $root module
  auto &root_ports = to_module_type(root_symbol.type).ports();

  for(auto top_level_module : top_level_modules)
  {
    auto module_identifier = verilog_module_symbol(top_level_module);
    auto &top_symbol = symbol_table.lookup_ref(module_identifier);
    for(auto &top_port : to_module_type(top_symbol.type).ports())
      root_ports.push_back(top_port);
  }

  auto add_result_root = symbol_table.add(root_symbol);
  CHECK_RETURN(!add_result_root);

  transition_system.main_symbol = symbol_table.lookup(root_identifier);

  const bool ignore_initial = cmdline.isset("ignore-initial");
  const bool initial_zero = cmdline.isset("initial-zero");

  // Synthesize $root, which expands the top-level module instance
  transition_system.trans_expr = verilog_synthesis(
    symbol_table,
    root_identifier,
    standard,
    ignore_initial,
    initial_zero,
    message_handler);
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

  // Random access into the parse tree list, which is a std::list.
  std::vector<const parse_treet *> vector;
  vector.reserve(parse_trees.size());

  for(auto &parse_tree : parse_trees)
    vector.push_back(&parse_tree);

  // A package is elaborated before the compilation units that import it,
  // which is the order in which the files were parsed.
  for(auto i : elaboration_order)
  {
    DATA_INVARIANT(i < vector.size(), "elaboration order must be in range");
    verilog_elaborate_compilation_unit(
      *vector[i], warn_implicit_nets, symbol_table, message_handler);
  }

  return symbol_table;
}

/// Collect all module base names that are instantiated by the given
/// parse trees, recursively descending into generate blocks.
static void collect_module_dependencies_rec(
  const verilog_module_itemt &module_item,
  std::set<irep_idt> &deps)
{
  if(module_item.id() == ID_inst)
  {
    deps.insert(to_verilog_inst(module_item).module_base_name());
  }
  else if(module_item.id() == ID_generate_block)
  {
    for(auto &sub_item : to_verilog_generate_block(module_item).module_items())
      collect_module_dependencies_rec(sub_item, deps);
  }
  else if(module_item.id() == ID_generate_if)
  {
    auto &generate_if = to_verilog_generate_if(module_item);
    collect_module_dependencies_rec(generate_if.then_case(), deps);
    if(generate_if.has_else_case())
      collect_module_dependencies_rec(generate_if.else_case(), deps);
  }
  else if(module_item.id() == ID_generate_for)
  {
    collect_module_dependencies_rec(
      to_verilog_generate_for(module_item).body(), deps);
  }
}

static std::set<irep_idt> collect_all_dependencies(
  const verilog_ebmc_languaget::parse_treest &parse_trees)
{
  std::set<irep_idt> deps;

  for(auto &parse_tree : parse_trees)
    for(auto &item : parse_tree.items)
      if(
        item.id() == ID_verilog_module || item.id() == ID_verilog_program ||
        item.id() == ID_verilog_checker)
      {
        for(auto &module_item : to_verilog_module_source(item).items())
          collect_module_dependencies_rec(module_item, deps);
      }

  return deps;
}

static std::set<irep_idt>
collect_all_provided(const verilog_ebmc_languaget::parse_treest &parse_trees)
{
  std::set<irep_idt> provided;

  for(auto &parse_tree : parse_trees)
    for(auto &item : parse_tree.items)
      if(
        item.id() == ID_verilog_module || item.id() == ID_verilog_checker ||
        item.id() == ID_verilog_interface)
      {
        provided.insert(to_verilog_module_source(item).base_name());
      }

  return provided;
}

void verilog_ebmc_languaget::resolve_library_modules(parse_treest &parse_trees)
{
  std::list<std::string> library_dirs;

  for(auto &dir : cmdline.get_values('y'))
    library_dirs.push_back(dir);

  for(auto &dir : cmdline.get_values("libdir"))
    library_dirs.push_back(dir);

  // Get file extensions from +libext+, or default to .v and .sv
  auto &libext_values = cmdline.get_values("libext");
  std::vector<std::string> extensions;

  if(!libext_values.empty())
  {
    for(auto &ext : libext_values)
      extensions.push_back(ext);
  }
  else
  {
    extensions.push_back(".v");
    extensions.push_back(".sv");
  }

  messaget log{message_handler};

  // Iteratively resolve library dependencies until no new
  // unresolved modules are found.
  while(true)
  {
    auto provided = collect_all_provided(parse_trees);
    auto dependencies = collect_all_dependencies(parse_trees);

    // Determine which dependencies are unresolved
    std::set<irep_idt> unresolved;
    for(auto &dep : dependencies)
      if(provided.find(dep) == provided.end())
        unresolved.insert(dep);

    if(unresolved.empty())
      break;

    bool found_any = false;

    for(auto &module_name : unresolved)
    {
      bool found = false;

      for(auto &dir : library_dirs)
      {
        for(auto &ext : extensions)
        {
          auto path =
            std::filesystem::path{dir} / (id2string(module_name) + ext);

          if(std::filesystem::exists(path))
          {
            log.status() << "Library: parsing " << path << messaget::eom;

            verilog_scopest scopes;
            parse_trees.push_back(parse(path, scopes));
            // Library files are parsed after the files given on the command
            // line, and are elaborated in that order also.
            elaboration_order.push_back(parse_trees.size() - 1);
            found = true;
            found_any = true;
            break;
          }
        }

        if(found)
          break;
      }
    }

    // If no new files were found in this iteration, stop.
    if(!found_any)
      break;
  }
}

void verilog_ebmc_languaget::create_reset_logic(
  const std::string &reset_constraint_string,
  transition_systemt &transition_system)
{
  auto language = get_language_from_mode(transition_system.main_symbol->mode);
  exprt reset_constraint;
  const namespacet ns{transition_system.symbol_table};

  if(language->to_expr(
       reset_constraint_string,
       id2string(transition_system.main_symbol->module),
       reset_constraint,
       ns,
       message_handler))
  {
    throw ebmc_errort{} << "failed to parse reset constraint";
  }

  // must be boolean, and we lower it
  auto reset_constraint_lowered = verilog_lowering(
    typecast_exprt::conditional_cast(reset_constraint, bool_typet{}));

  // true in initial state
  transt new_trans_expr = transition_system.trans_expr;
  new_trans_expr.init() =
    and_exprt(new_trans_expr.init(), reset_constraint_lowered);

  // and not anymore afterwards
  exprt reset_next_state = reset_constraint_lowered;
  make_next_state(reset_next_state);

  new_trans_expr.trans() =
    and_exprt(new_trans_expr.trans(), not_exprt(reset_next_state));
  transition_system.trans_expr = new_trans_expr;
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

  // resolve library directories (-y)
  if(cmdline.isset('y') || cmdline.isset("libdir"))
    resolve_library_modules(parse_trees);

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
  auto library_count =
    cmdline.get_values('l').size() + cmdline.get_values("libfile").size();
  auto top_level_modules =
    ::top_level_modules(parse_trees, cmdline, library_count);

  //
  // type checking
  //

  message.status() << "Converting" << messaget::eom;

  auto transition_system =
    typecheck(parse_trees, top_level_modules, std::move(symbol_table));

  // Create the $root module instance and synthesize it
  create_root_module(
    top_level_modules, parse_trees.front().standard, transition_system);

  if(cmdline.isset("show-symbol-table"))
  {
    std::cout << transition_system.symbol_table;
    return {};
  }

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
    create_reset_logic(cmdline.get_value("reset"), transition_system);

  // done with the transition system
  return transition_system;
}
