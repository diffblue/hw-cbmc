/*******************************************************************\

Module: SMV Parse Tree Index

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "smv_index.h"

#include "smv_expr.h"

smv_indext::smv_indext(smv_parse_treet &parse_tree)
{
  // module map
  for(auto module_it = parse_tree.module_list.begin();
      module_it != parse_tree.module_list.end();
      module_it++)
  {
    module_map[module_it->base_name] = module_it;
  }

  // enums
  for(const auto &module : parse_tree.module_list)
  {
    for(const auto &element : module.elements)
    {
      if(element.is_enum())
      {
        const auto &identifier_expr = to_smv_identifier_expr(element.expr);
        irep_idt base_name = identifier_expr.identifier();
        enum_names.insert(base_name);
      }
    }
  }
}
