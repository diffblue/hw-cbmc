/*******************************************************************\

Module: Verilog Elaboration

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_typecheck.h"

/*******************************************************************\

Function: verilog_typecheckt::elaborate_inst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_inst(
  const verilog_inst_baset &inst_module_item)
{
  for(auto &instance : inst_module_item.instances())
    elaborate_inst(inst_module_item, instance);
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_inst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_inst(
  const verilog_inst_baset &statement,
  const verilog_instt::instancet &op)
{
  if(op.instance_array().is_not_nil())
  {
    throw errort().with_location(op.source_location())
      << "no support for instance arrays";
  }

  bool primitive = statement.id() == ID_inst_builtin;
  const exprt &range_expr = static_cast<const exprt &>(op.find(ID_range));

  ranget range;

  if(range_expr.is_nil() || range_expr.id().empty())
    range = ranget{0, 0};
  else
    range = convert_range(range_expr);

  irep_idt instantiated_module_identifier =
    verilog_module_symbol(id2string(statement.get(ID_module)));

  // add symbol for the module instance
  symbolt symbol;

  symbol.mode = mode;
  symbol.base_name = op.base_name();
  symbol.type =
    typet(primitive ? ID_primitive_module_instance : ID_module_instance);
  symbol.module = module_identifier;
  symbol.name = hierarchical_identifier(symbol.base_name);
  symbol.pretty_name = strip_verilog_prefix(symbol.name);
  symbol.value.set(ID_module, instantiated_module_identifier);

  if(symbol_table.add(symbol))
  {
    throw errort().with_location(op.source_location())
      << "duplicate definition of identifier `" << symbol.base_name
      << "' in module `" << module_symbol.base_name << '\'';
  }
}

/*******************************************************************\

Function: verilog_typecheckt::elaboate_module_instances

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_module_instances(
  const verilog_module_itemt &module_item)
{
  if(module_item.id() == ID_inst)
  {
    elaborate_inst(to_verilog_inst(module_item));
  }
  else if(module_item.id() == ID_inst_builtin)
  {
    elaborate_inst(to_verilog_inst_builtin(module_item));
  }
  else if(module_item.id() == ID_generate_block)
  {
    auto &generate_block = to_verilog_generate_block(module_item);

    // These introduce scope, much like a named block statement.
    bool is_named = generate_block.is_named();

    if(is_named)
    {
      irep_idt base_name = generate_block.base_name();
      enter_named_block(base_name);
    }

    for(auto &item : generate_block.module_items())
      elaborate_module_instances(item);

    if(is_named)
      named_blocks.pop_back();
  }
  else if(module_item.id() == ID_set_genvars)
  {
    elaborate_module_instances(
      to_verilog_set_genvars(module_item).module_item());
  }
}
