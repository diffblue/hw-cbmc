/*******************************************************************\

Module: Verilog Top Level Modules

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Verilog Top Level Modules

#include "top_level_modules.h"

#include <util/cmdline.h>

#include <ebmc/ebmc_error.h>

static void sort_alphabetically(std::vector<irep_idt> &names)
{
  std::sort(
    names.begin(),
    names.end(),
    [](const irep_idt &a, const irep_idt &b)
    { return id2string(a) < id2string(b); });
}

static void module_dependencies_rec(
  const verilog_module_itemt &module_item,
  const std::function<void(irep_idt)> &action)
{
  if(module_item.id() == ID_inst)
  {
    action(to_verilog_inst(module_item).module_base_name());
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
std::vector<irep_idt> top_level_modules(
  const std::list<verilog_parse_treet> &parse_trees,
  const cmdlinet &cmdline)
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
        throw ebmc_errort{}.with_exit_code(2)
          << "module '" << given_module << "' not found";
      }
    }

    // now sort alphabetically
    sort_alphabetically(given_modules);

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
    throw ebmc_errort{}.with_exit_code(1) << "no module found";
  }

  // sort alphabetically into a vector
  std::vector<irep_idt> result;

  for(auto &module : top_level_modules)
    result.push_back(module);

  sort_alphabetically(result);

  return result; // done
}
