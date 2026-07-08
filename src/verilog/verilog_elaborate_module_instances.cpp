/*******************************************************************\

Module: Verilog Elaboration

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/mathematical_types.h>

#include "verilog_typecheck.h"
#include "verilog_types.h"

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
    elaborate_instance_array(statement, op);
    return;
  }

  bool primitive = statement.id() == ID_inst_builtin;
  const exprt &range_expr = static_cast<const exprt &>(op.find(ID_range));

  ranget range;

  if(range_expr.is_nil() || range_expr.id().empty())
    range = ranget{0, 0};
  else
    range = convert_range(range_expr);

  irep_idt instantiated_module_identifier =
    verilog_module_symbol(statement.module_base_name());

  // add symbol for the module instance
  symbolt symbol;

  symbol.mode = mode;
  symbol.base_name = op.base_name();
  symbol.type = typet{
    primitive ? ID_primitive_module_instance : ID_verilog_module_instance};
  symbol.module = verilog_root_module_identifier();
  symbol.name = hierarchical_identifier(symbol.base_name);
  symbol.pretty_name = strip_verilog_root_prefix(symbol.name);
  symbol.value = verilog_module_instancet{instantiated_module_identifier};

  if(symbol_table.add(symbol))
  {
    throw errort().with_location(op.source_location())
      << "duplicate definition of identifier `" << symbol.base_name
      << "' in module `" << module_symbol().base_name << '\'';
  }
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_instance_array

  Inputs:

 Outputs:

 Purpose: Creates individual instance symbols for an instance array.
          For an array declaration like "simple_if bus[2]()", this
          creates symbols bus[0] and bus[1].

\*******************************************************************/

void verilog_typecheckt::elaborate_instance_array(
  const verilog_inst_baset &statement,
  const verilog_instt::instancet &op)
{
  bool primitive = statement.id() == ID_inst_builtin;

  irep_idt instantiated_module_identifier =
    verilog_module_symbol(statement.module_base_name());

  const auto &array_type = op.instance_array();

  // Determine the array range.
  mp_integer lo, hi;

  if(array_type.id() == ID_verilog_unpacked_array)
  {
    // Check for multi-dimensional instance arrays (not yet supported).
    // The subtype of the unpacked_dimension contains nested dimensions.
    auto &subtype = to_type_with_subtype(array_type).subtype();
    if(subtype.id() == ID_verilog_unpacked_array)
    {
      throw errort().with_location(op.source_location())
        << "no support for multi-dimensional instance arrays";
    }

    const auto &size_expr =
      static_cast<const exprt &>(array_type.find(ID_size));
    const auto &range_expr =
      static_cast<const exprt &>(array_type.find(ID_range));

    if(size_expr.is_not_nil())
    {
      // [N] form: indices 0..N-1
      mp_integer size = convert_integer_constant_expression(size_expr);
      lo = 0;
      hi = size - 1;
    }
    else if(range_expr.is_not_nil())
    {
      // [msb:lsb] form
      auto range = convert_range(range_expr);
      if(range.msb >= range.lsb)
      {
        lo = range.lsb;
        hi = range.msb;
      }
      else
      {
        lo = range.msb;
        hi = range.lsb;
      }
    }
    else
    {
      throw errort().with_location(op.source_location())
        << "instance array has no size or range";
    }
  }
  else
  {
    throw errort().with_location(op.source_location())
      << "unexpected instance array type";
  }

  // Create a parent array symbol for name resolution of bus[i].
  {
    mp_integer array_size = hi - lo + 1;

    symbolt array_symbol;
    array_symbol.mode = mode;
    array_symbol.base_name = op.base_name();
    array_symbol.type = verilog_array_typet{
      ID_verilog_unpacked_array,
      typet{
        primitive ? ID_primitive_module_instance : ID_verilog_module_instance},
      array_size,
      lo,
      true};
    array_symbol.module = verilog_root_module_identifier();
    array_symbol.name = hierarchical_identifier(op.base_name());
    array_symbol.pretty_name = strip_verilog_root_prefix(array_symbol.name);
    array_symbol.value.make_nil();

    if(symbol_table.add(array_symbol))
    {
      throw errort().with_location(op.source_location())
        << "duplicate definition of identifier `" << op.base_name()
        << "' in module `" << module_symbol().base_name << '\'';
    }
  }

  // Create one instance symbol per array index.
  for(mp_integer i = lo; i <= hi; ++i)
  {
    std::string indexed_base_name =
      id2string(op.base_name()) + '[' + integer2string(i) + ']';

    symbolt symbol;

    symbol.mode = mode;
    symbol.base_name = indexed_base_name;
    symbol.type = typet{
      primitive ? ID_primitive_module_instance : ID_verilog_module_instance};
    symbol.module = verilog_root_module_identifier();
    symbol.name = hierarchical_identifier(indexed_base_name);
    symbol.pretty_name = strip_verilog_root_prefix(symbol.name);
    symbol.value = verilog_module_instancet{instantiated_module_identifier};

    if(symbol_table.add(symbol))
    {
      throw errort().with_location(op.source_location())
        << "duplicate definition of identifier `" << indexed_base_name
        << "' in module `" << module_symbol().base_name << '\'';
    }
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
    exprt lhs = assignment.lhs();

    // the lhs must be instance.parameter
    if(lhs.id() != ID_hierarchical_identifier)
    {
      throw errort().with_location(module_item.source_location())
        << "defparam expected to have a hierachical identifier";
    }

    auto &hierarchical_identifier = to_hierarchical_identifier_expr(lhs);

    // convert the instance
    convert_expr(hierarchical_identifier.module_instance());

    if(hierarchical_identifier.module_instance().id() != ID_symbol)
    {
      throw errort().with_location(module_item.source_location())
        << "defparam expected to have a single level identifier";
    }

    auto module_instance =
      to_symbol_expr(hierarchical_identifier.module_instance()).identifier();

    auto parameter_base_name = hierarchical_identifier.item().base_name();

    // The rhs must be a constant at this point.
    auto rhs_value = from_integer(
      convert_integer_constant_expression(assignment.rhs()), integer_typet{});

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
  const irep_idt &inst_module = inst.module_base_name();

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
        // constant-fold
        convert_expr(value);
        value =
          elaborate_constant_expression_check(value).with_source_location(*it);
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
        // constant-fold
        convert_expr(*it);
        *it =
          elaborate_constant_expression_check(*it).with_source_location(*it);
      }
    }
  }

  // get the instance symbols
  for(auto &instance : inst.instances())
  {
    if(instance.instance_array().is_not_nil())
    {
      // Instance array: parameterize each element.
      parameterize_instance_array(
        inst, instance, module_identifier, parameter_assignments);
    }
    else
    {
      const auto instance_base_name = instance.base_name();

      const irep_idt instance_identifier =
        hierarchical_identifier(instance_base_name);

      // add relevant defparam assignments
      auto &instance_defparams = defparams[instance_identifier];

      irep_idt new_module_identifier = instantiate_module(
        inst.source_location(),
        module_identifier,
        inst_module,
        instance_identifier,
        parameter_assignments,
        instance_defparams);

      instance.identifier(instance_identifier);
      instance.module_identifier(new_module_identifier);

      symbolt &instance_symbol = symbol_table_lookup(instance_identifier);

      // fix the module in the instance symbol
      instance_symbol.value.set(ID_module, new_module_identifier);

      const symbolt &parameterized_module_symbol =
        symbol_table_lookup(new_module_identifier);

      // check the port connections
      typecheck_port_connections(instance, parameterized_module_symbol);
    }
  }
}

/*******************************************************************\

Function: verilog_typecheckt::parameterize_instance_array

  Inputs:

 Outputs:

 Purpose: Parameterizes each element of an instance array.

\*******************************************************************/

void verilog_typecheckt::parameterize_instance_array(
  verilog_instt &inst,
  verilog_instt::instancet &instance,
  const irep_idt &module_identifier,
  exprt::operandst &parameter_assignments)
{
  const irep_idt &inst_module = inst.module_base_name();
  const auto &array_type = instance.instance_array();

  // Determine the array range.
  mp_integer lo, hi;

  if(array_type.id() == ID_verilog_unpacked_array)
  {
    const auto &size_expr =
      static_cast<const exprt &>(array_type.find(ID_size));
    const auto &range_expr =
      static_cast<const exprt &>(array_type.find(ID_range));

    if(size_expr.is_not_nil())
    {
      mp_integer size = convert_integer_constant_expression(size_expr);
      lo = 0;
      hi = size - 1;
    }
    else if(range_expr.is_not_nil())
    {
      auto range = convert_range(range_expr);
      if(range.msb >= range.lsb)
      {
        lo = range.lsb;
        hi = range.msb;
      }
      else
      {
        lo = range.msb;
        hi = range.lsb;
      }
    }
    else
    {
      throw errort().with_location(instance.source_location())
        << "instance array has no size or range";
    }
  }
  else
  {
    throw errort().with_location(instance.source_location())
      << "unexpected instance array type";
  }

  // Store the array parent identifier on the instance for synthesis.
  const irep_idt array_identifier =
    hierarchical_identifier(instance.base_name());
  instance.identifier(array_identifier);

  for(mp_integer i = lo; i <= hi; ++i)
  {
    std::string indexed_base_name =
      id2string(instance.base_name()) + '[' + integer2string(i) + ']';

    const irep_idt instance_identifier =
      hierarchical_identifier(indexed_base_name);

    // add relevant defparam assignments
    auto &instance_defparams = defparams[instance_identifier];

    irep_idt new_module_identifier = instantiate_module(
      inst.source_location(),
      module_identifier,
      inst_module,
      instance_identifier,
      parameter_assignments,
      instance_defparams);

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
  const irep_idt &inst_module = inst.module_base_name();

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
