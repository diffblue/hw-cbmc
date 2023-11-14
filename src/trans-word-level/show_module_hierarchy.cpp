/*******************************************************************\

Module: Show Module Hierarchy

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "show_module_hierarchy.h"

#include <util/namespace.h>

std::size_t hierarchy_depth(const irep_idt &identifier)
{
  auto &as_string = id2string(identifier);
  return std::count(as_string.begin(), as_string.end(), '.');
}

void show_module_hierarchy(
  const symbol_table_baset &symbol_table,
  const symbolt &main_symbol,
  std::ostream &out)
{
  // Get the sorted list of symbols and
  // find any module instances in the given module.
  std::vector<irep_idt> instances;

  for(auto &identifier : symbol_table.sorted_symbol_names())
  {
    const auto &symbol = symbol_table.lookup_ref(identifier);
    if(
      symbol.type.id() == ID_module_instance &&
      symbol.module == main_symbol.name)
    {
      instances.push_back(identifier);
    }
  }

  // now display them as a tree, using the 'main_symbol' as the root
  out << main_symbol.display_name() << ':' << '\n';

  for(const auto &identifier : instances)
  {
    const auto &symbol = symbol_table.lookup_ref(identifier);

    // indent according to depth in the hierarchy
    out << std::string(hierarchy_depth(identifier) * 2, ' ');

    // output type
    auto instance_module = symbol.value.get(ID_module);
    if(!instance_module.empty())
    {
      const auto &module_symbol = symbol_table.lookup_ref(instance_module);
      out << module_symbol.pretty_name << ' ';
    }

    // then instance name
    out << symbol.display_name() << '\n';
  }
}
