/*******************************************************************\

Module: Verilog Elaboration

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/mathematical_types.h>

#include "verilog_typecheck.h"

/*******************************************************************\

Function: verilog_typecheckt::process_module_instantiations

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::process_module_instantiations(
  verilog_module_exprt &verilog_module_expr)
{
  // Module instantiations are processed in three steps:
  // 1. Create a symbol S for each instance
  // 2. Get values for all defparam S.parameter = ... items.
  // 3. Parameterize the module with the parameters.

  // create the module instance symbols
  for(auto &module_item : verilog_module_expr.module_items())
    elaborate_module_instances(module_item);

  // defparam
  for(auto &module_item : verilog_module_expr.module_items())
    process_parameter_override(module_item);

  // now parameterize the instantiated modules
  for(auto &module_item : verilog_module_expr.module_items())
    parameterize_instantiated_modules(module_item);
}

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

/*******************************************************************\

Function: verilog_typecheckt::process_parameter_override

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::process_parameter_override(
  const verilog_parameter_overridet &module_item)
{
  for(auto &assignment : module_item.assignments())
  {
    // Copy the lhs/rhs.
    exprt lhs = to_binary_expr(assignment).lhs();
    exprt rhs = to_binary_expr(assignment).rhs();

    // The lhs is a sequence of module instance names using
    // hierarchical_identifier expressions.
    convert_expr(lhs);

    // turn into identifier
    if(lhs.id() != ID_hierarchical_identifier)
    {
      throw errort().with_location(module_item.source_location())
        << "defparam expected to have a hierachical identifier";
    }

    const auto &hierarchical_identifier = to_hierarchical_identifier_expr(lhs);

    if(hierarchical_identifier.module().id() != ID_symbol)
    {
      throw errort().with_location(module_item.source_location())
        << "defparam expected to have a single level identifier";
    }

    auto module_instance =
      to_symbol_expr(hierarchical_identifier.module()).get_identifier();
    auto parameter_base_name = hierarchical_identifier.item().base_name();

    // The rhs must be a constant at this point.
    auto rhs_value =
      from_integer(convert_integer_constant_expression(rhs), integer_typet());

    // store the assignment.
    defparams[module_instance][parameter_base_name] = rhs_value;
  }
}

/*******************************************************************\

Function: verilog_typecheckt::process_parameter_override

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::process_parameter_override(
  const verilog_module_itemt &item)
{
  // Do defparam, also known as 'parameter override'.
  // These must all be done before any module instantiation,
  // which use the parameters.
  if(item.id() == ID_parameter_override)
  {
    process_parameter_override(to_verilog_parameter_override(item));
  }
  else if(item.id() == ID_set_genvars)
  {
    for(auto &sub_item : item.operands())
    {
      if(sub_item.id() == ID_parameter_override)
        process_parameter_override(to_verilog_parameter_override(sub_item));
    }
  }
}

/*******************************************************************\

Function: verilog_typecheckt::parameterize_instantiated_modules

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::parameterize_instantiated_modules(
  verilog_module_itemt &module_item)
{
  if(module_item.id() == ID_inst)
  {
    parameterize_instantiated_modules(to_verilog_inst(module_item));
  }
  else if(module_item.id() == ID_inst_builtin)
  {
    parameterize_instantiated_modules(to_verilog_inst_builtin(module_item));
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
      parameterize_instantiated_modules(item);

    if(is_named)
      named_blocks.pop_back();
  }
  else if(module_item.id() == ID_set_genvars)
  {
    parameterize_instantiated_modules(
      to_verilog_set_genvars(module_item).module_item());
  }
}

/*******************************************************************\

Function: verilog_typecheckt::parameterize_instantiated_modules

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::parameterize_instantiated_modules(verilog_instt &inst)
{
  const irep_idt &inst_module = inst.get_module();

  // The instantiated module must be user-defined.

  const irep_idt module_identifier =
    verilog_module_symbol(id2string(inst_module));

  exprt::operandst &parameter_assignments = inst.parameter_assignments();

  Forall_expr(it, parameter_assignments)
  {
    // These must be constants. Preserve the location.
    if(it->id() == ID_named_parameter_assignment)
    {
      auto &value = static_cast<exprt &>(it->add(ID_value));
      if(value.id() == ID_type)
      {
        // leave as is
      }
      else
      {
        mp_integer v_int = convert_integer_constant_expression(value);
        value = from_integer(v_int, integer_typet()).with_source_location(*it);
      }
    }
    else
    {
      if(it->id() == ID_type)
      {
        // leave as is
      }
      else
      {
        mp_integer v_int = convert_integer_constant_expression(*it);
        *it = from_integer(v_int, integer_typet()).with_source_location(*it);
      }
    }
  }

  // get the instance symbols
  for(auto &instance : inst.instances())
  {
    const auto instance_base_name = instance.base_name();

    const irep_idt instance_identifier =
      hierarchical_identifier(instance_base_name);

    instance.identifier(instance_identifier);

    // add relevant defparam assignments
    auto &instance_defparams = defparams[instance_identifier];

    irep_idt new_module_identifier = parameterize_module(
      inst.source_location(),
      module_identifier,
      parameter_assignments,
      instance_defparams);

    inst.set_module(new_module_identifier);

    symbolt &instance_symbol = symbol_table_lookup(instance_identifier);

    // fix the module in the instance symbol
    instance_symbol.value.set(ID_module, new_module_identifier);

    const symbolt &parameterized_module_symbol =
      symbol_table_lookup(new_module_identifier);

    // check the port connections
    typecheck_port_connections(instance, parameterized_module_symbol);
  }
}

/*******************************************************************\

Function: verilog_typecheckt::parameterize_instantiated_modules

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::parameterize_instantiated_modules(
  verilog_inst_builtint &inst)
{
  const irep_idt &inst_module = inst.get_module();

  for(auto &instance : inst.instances())
  {
    typecheck_builtin_port_connections(instance);

    // check built-in ones
    if(
      inst_module == ID_bufif0 || inst_module == ID_bufif1 ||
      inst_module == ID_notif0 || inst_module == ID_notif1)
    {
    }
    else if(
      inst_module == ID_nmos || inst_module == ID_pmos ||
      inst_module == ID_rnmos || inst_module == ID_rpmos)
    {
    }
    else if(
      inst_module == ID_and || inst_module == ID_nand || inst_module == ID_or ||
      inst_module == ID_nor || inst_module == ID_xor || inst_module == ID_xnor)
    {
      if(instance.connections().size() < 2)
      {
        throw errort().with_location(instance.source_location())
          << "Primitive gate " << inst_module
          << " expects at least two operands";
      }
    }
    else if(inst_module == ID_buf || inst_module == ID_not)
    {
      if(instance.connections().size() < 2)
      {
        throw errort().with_location(instance.source_location())
          << "Primitive gate " << inst_module
          << " expects at least two operands";
      }
    }
    else if(
      inst_module == "tranif0" || inst_module == "tranif1" ||
      inst_module == "rtranif1" || inst_module == "rtranif0")
    {
    }
    else if(inst_module == "tran" || inst_module == "rtran")
    {
    }
    else
    {
      throw errort().with_location(inst.source_location())
        << "Unknown primitive Verilog module " << inst_module;
    }
  }
}
