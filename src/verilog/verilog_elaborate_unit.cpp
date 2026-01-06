/*******************************************************************\

Module: Elaboration of Verilog Compilation Units

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_elaborate_unit.h"

#include "verilog_typecheck.h"

void verilog_elaborate_unit(
  const verilog_parse_treet &parse_tree,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  bool warn_implicit_nets = false;

  for(auto &item : parse_tree.items)
  {
    if(item.id() == ID_verilog_module)
    {
      auto base_name = to_verilog_module_source(item).base_name();
      auto module_identifier = verilog_module_symbol(base_name);

      auto error = verilog_typecheck(
        parse_tree,
        symbol_table,
        module_identifier,
        warn_implicit_nets,
        message_handler);

      if(error)
      {
      }
    }
  }
}
