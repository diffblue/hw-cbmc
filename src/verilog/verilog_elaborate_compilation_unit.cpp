/*******************************************************************\

Module: Elaboration of Verilog Compilation Units

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_elaborate_compilation_unit.h"

#include "verilog_typecheck.h"

void verilog_elaborate_compilation_unit(
  const verilog_parse_treet &parse_tree,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  for(auto &item : parse_tree.items)
  {
    if(item.id() == ID_verilog_module || item.id() == ID_verilog_checker)
    {
      auto identifier =
        verilog_module_symbol(to_verilog_module_source(item).base_name());
      copy_module_source(item, identifier, symbol_table);
    }
    else if(item.id() == ID_verilog_package)
    {
      auto identifier =
        verilog_package_identifier(to_verilog_module_source(item).base_name());
      copy_module_source(item, identifier, symbol_table);
    }
  }
}
