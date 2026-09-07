/*******************************************************************\

Module: Verilog Elaboration

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/mathematical_types.h>
#include <util/std_expr.h>

#include "verilog_typecheck.h"
#include "verilog_types.h"

#include <optional>
#include <set>

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
    // 1800-2017 23.3.2: an array of instances
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

Function: verilog_typecheckt::instance_array_dimensions

  Inputs:

 Outputs:

 Purpose: Extracts the dimensions of an instance array,
          outermost (leftmost) dimension first, with the
          indices as written. Per 1800-2017 23.3.2, a dimension
          [size] is equivalent to [0:size-1].

\*******************************************************************/

verilog_typecheckt::instance_array_dimst
verilog_typecheckt::instance_array_dimensions(
  const typet &instance_array,
  const source_locationt &source_location)
{
  instance_array_dimst dims;

  for(const typet *t = &instance_array; t->id() == ID_verilog_unpacked_array;
      t = &to_type_with_subtype(*t).subtype())
  {
    const exprt &range_expr = static_cast<const exprt &>(t->find(ID_range));
    const exprt &size_expr = static_cast<const exprt &>(t->find(ID_size));

    instance_array_dimt dim;

    if(range_expr.is_not_nil())
    {
      // [left:right]
      auto range = convert_range(range_expr);
      dim.left = range.msb;
      dim.right = range.lsb;
    }
    else if(size_expr.is_not_nil())
    {
      // [size] is short for [0:size-1]
      mp_integer size = convert_integer_constant_expression(size_expr);

      if(size <= 0)
      {
        throw errort().with_location(source_location)
          << "instance array size must be positive";
      }

      dim.left = 0;
      dim.right = size - 1;
    }
    else
    {
      throw errort().with_location(source_location)
        << "instance array dimension must have a range or a size";
    }

    dims.push_back(std::move(dim));
  }

  return dims;
}

/*******************************************************************\

Function: instance_array_suffixes

  Inputs:

 Outputs:

 Purpose: Enumerates the element name suffixes of an instance
          array in declaration order, i.e., the element given
          by the leftmost index of every dimension comes first.
          E.g., the dimensions [1:0][2] yield the suffixes
          [1][0], [1][1], [0][0], [0][1].

\*******************************************************************/

static std::vector<std::string>
instance_array_suffixes(const verilog_typecheckt::instance_array_dimst &dims)
{
  std::vector<std::string> result{""};

  for(auto &dim : dims)
  {
    std::vector<std::string> next;
    next.reserve(result.size() * numeric_cast_v<std::size_t>(dim.size()));

    const mp_integer step = dim.left <= dim.right ? 1 : -1;

    for(auto &prefix : result)
    {
      for(mp_integer i = dim.left;; i += step)
      {
        next.push_back(prefix + '[' + integer2string(i) + ']');
        if(i == dim.right)
          break;
      }
    }

    result = std::move(next);
  }

  return result;
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_instance_array

  Inputs:

 Outputs:

 Purpose: Creates the symbols for an array of instances
          (1800-2017 23.3.2): one symbol per element, plus a
          symbol for the array itself, which is used to resolve
          hierarchical references to the elements.

\*******************************************************************/

void verilog_typecheckt::elaborate_instance_array(
  const verilog_inst_baset &statement,
  const verilog_instt::instancet &op)
{
  bool primitive = statement.id() == ID_inst_builtin;

  irep_idt instantiated_module_identifier =
    verilog_module_symbol(statement.module_base_name());

  auto dims =
    instance_array_dimensions(op.instance_array(), op.source_location());

  const typet instance_type{
    primitive ? ID_primitive_module_instance : ID_verilog_module_instance};

  // The symbol for the array itself.
  {
    typet array_type = instance_type;

    for(auto it = dims.rbegin(); it != dims.rend(); ++it)
    {
      array_type = verilog_array_typet{
        ID_verilog_unpacked_array,
        std::move(array_type),
        it->size(),
        std::min(it->left, it->right),
        it->left < it->right};
    }

    symbolt symbol;

    symbol.mode = mode;
    symbol.base_name = op.base_name();
    symbol.type = std::move(array_type);
    symbol.module = verilog_root_module_identifier();
    symbol.name = hierarchical_identifier(symbol.base_name);
    symbol.pretty_name = strip_verilog_root_prefix(symbol.name);
    symbol.value = nil_exprt{};

    if(symbol_table.add(symbol))
    {
      throw errort().with_location(op.source_location())
        << "duplicate definition of identifier `" << symbol.base_name
        << "' in module `" << module_symbol().base_name << '\'';
    }
  }

  // One symbol per element of the array.
  for(auto &suffix : instance_array_suffixes(dims))
  {
    irep_idt element_base_name = id2string(op.base_name()) + suffix;

    symbolt symbol;

    symbol.mode = mode;
    symbol.base_name = element_base_name;
    symbol.type = instance_type;
    symbol.module = verilog_root_module_identifier();
    symbol.name = hierarchical_identifier(element_base_name);
    symbol.pretty_name = strip_verilog_root_prefix(symbol.name);
    symbol.value = verilog_module_instancet{instantiated_module_identifier};

    if(symbol_table.add(symbol))
    {
      throw errort().with_location(op.source_location())
        << "duplicate definition of identifier `" << symbol.base_name
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
    // Restore the genvar values that were in effect when this generate
    // item was elaborated. Parameter assignments and port connections of
    // the enclosed instance may refer to genvars (e.g. an output connected
    // to arr[g]); without this the live genvars map still holds the
    // post-loop value and such references are mis-evaluated. This mirrors
    // the restore done in convert_module_item.
    auto saved_genvars = genvars;
    genvars.clear();
    const auto &variables = to_verilog_set_genvars(module_item).variables();
    for(auto &var : variables)
      genvars[id2string(var.first)] = string2integer(var.second.id_string());

    parameterize_instantiated_modules(
      to_verilog_set_genvars(module_item).module_item());

    genvars = std::move(saved_genvars);
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
  verilog_instt::instancest new_instances;
  new_instances.reserve(inst.instances().size());

  for(auto &instance : inst.instances())
  {
    if(instance.instance_array().is_not_nil())
    {
      // 1800-2017 23.3.2: expand the instance array into
      // one instance per element
      expand_instance_array(
        inst,
        instance,
        module_identifier,
        parameter_assignments,
        new_instances);
      continue;
    }

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

    new_instances.push_back(std::move(instance));
  }

  inst.instances() = std::move(new_instances);
}

/*******************************************************************\

Function: verilog_typecheckt::expand_instance_array

  Inputs:

 Outputs:

 Purpose: Expands an array of instances (1800-2017 23.3.2) into
          one instance per element, splitting up the port
          connections as required by 1800-2017 23.3.3.

\*******************************************************************/

void verilog_typecheckt::expand_instance_array(
  const verilog_instt &inst,
  const verilog_instt::instancet &instance,
  const irep_idt &module_identifier,
  const exprt::operandst &parameter_assignments,
  verilog_instt::instancest &dest)
{
  const irep_idt &inst_module = inst.module_base_name();

  auto dims = instance_array_dimensions(
    instance.instance_array(), instance.source_location());

  auto suffixes = instance_array_suffixes(dims);

  const mp_integer number_of_elements = suffixes.size();

  // Instantiate the module for each element of the array.
  std::vector<irep_idt> element_base_names, element_identifiers,
    element_modules;

  element_base_names.reserve(suffixes.size());
  element_identifiers.reserve(suffixes.size());
  element_modules.reserve(suffixes.size());

  for(auto &suffix : suffixes)
  {
    irep_idt element_base_name = id2string(instance.base_name()) + suffix;
    irep_idt element_identifier = hierarchical_identifier(element_base_name);

    // add relevant defparam assignments
    auto &instance_defparams = defparams[element_identifier];

    irep_idt element_module_identifier = instantiate_module(
      inst.source_location(),
      module_identifier,
      inst_module,
      element_identifier,
      parameter_assignments,
      instance_defparams);

    // fix the module in the instance symbol
    symbolt &element_symbol = symbol_table_lookup(element_identifier);
    element_symbol.value.set(ID_module, element_module_identifier);

    element_base_names.push_back(element_base_name);
    element_identifiers.push_back(element_identifier);
    element_modules.push_back(element_module_identifier);
  }

  // Now do the port connections. All elements have the same list
  // of ports; use the ports of the first element to resolve the
  // connections.
  const auto &first_ports =
    to_module_type(symbol_table_lookup(element_modules.front()).type).ports();

  // 'no connection' is one connection that is nil
  exprt::operandst connections = instance.connections();

  if(connections.size() == 1 && connections.front().is_nil())
    connections.clear();

  const bool named = instance.named_port_connections();

  // The connection values, converted, with the index of the port
  // they connect to.
  struct resolved_connectiont
  {
    std::size_t port_index;
    exprt value;
  };

  std::vector<resolved_connectiont> resolved_connections;
  resolved_connections.reserve(connections.size());

  auto convert_connection = [this](exprt &op)
  {
    if(op.is_nil())
    {
      // *not* connected
    }
    else if(op.id() == ID_verilog_identifier)
    {
      // IEEE 1800 2017 6.10 allows implicit declarations of nets when
      // used in a port connection.
      op = convert_verilog_identifier(
        to_verilog_identifier_expr(op), bool_typet{});
    }
    else
      convert_expr(op);
  };

  if(named)
  {
    std::set<irep_idt> assigned_ports;

    for(auto &connection : connections)
    {
      if(connection.id() == ID_verilog_wildcard_port_connection)
      {
        throw errort{}.with_location(connection.source_location())
          << "no support for wildcard port connections on instance arrays";
      }

      if(connection.id() != ID_verilog_named_port_connection)
      {
        throw errort().with_location(instance.source_location())
          << "expected a named port connection";
      }

      auto &named_port_connection =
        to_verilog_named_port_connection(connection);

      const irep_idt &base_name =
        to_verilog_identifier_expr(named_port_connection.port()).base_name();

      if(assigned_ports.find(base_name) != assigned_ports.end())
      {
        throw errort().with_location(connection.source_location())
          << "port name " << base_name << " assigned twice";
      }

      assigned_ports.insert(base_name);

      std::optional<std::size_t> port_index;

      for(std::size_t p = 0; p < first_ports.size(); p++)
        if(first_ports[p].base_name() == base_name)
        {
          port_index = p;
          break;
        }

      if(!port_index.has_value())
      {
        throw errort().with_location(connection.source_location())
          << "port name " << base_name << " not found";
      }

      exprt value = named_port_connection.value();
      convert_connection(value);

      resolved_connections.push_back({*port_index, std::move(value)});
    }
  }
  else // positional connections
  {
    if(connections.size() != first_ports.size())
    {
      throw errort().with_location(instance.source_location())
        << "wrong number of port connections: expected " << first_ports.size()
        << " but got " << connections.size();
    }

    for(std::size_t p = 0; p < connections.size(); p++)
    {
      exprt value = connections[p];
      convert_connection(value);
      resolved_connections.push_back({p, std::move(value)});
    }
  }

  // Create one instance per element of the array.
  for(std::size_t k = 0; k < suffixes.size(); k++)
  {
    const auto &ports =
      to_module_type(symbol_table_lookup(element_modules[k]).type).ports();

    exprt::operandst element_connections;
    element_connections.reserve(resolved_connections.size());

    for(auto &resolved : resolved_connections)
    {
      const auto &port = ports[resolved.port_index];

      exprt element_value = resolved.value.is_nil()
                              ? resolved.value
                              : instance_array_element_connection(
                                  resolved.value,
                                  port.type(),
                                  dims,
                                  number_of_elements,
                                  k,
                                  instance.source_location());

      if(element_value.is_not_nil())
      {
        // like typecheck_port_connection
        if(port.output())
          check_lhs(element_value, A_CONTINUOUS);
        else if(port.direction() != ID_verilog_ref)
          assignment_conversion(element_value, port.type());
      }

      if(named)
      {
        auto port_expr =
          symbol_exprt{port.identifier(), port.type()}.with_source_location(
            instance.source_location());

        element_connections.push_back(
          verilog_inst_baset::named_port_connectiont{
            std::move(port_expr), std::move(element_value)});
      }
      else
        element_connections.push_back(std::move(element_value));
    }

    verilog_instt::instancet element = instance; // copy
    element.remove(ID_verilog_instance_array);
    element.base_name(element_base_names[k]);
    element.identifier(element_identifiers[k]);
    element.module_identifier(element_modules[k]);
    element.connections() = std::move(element_connections);

    dest.push_back(std::move(element));
  }
}

/*******************************************************************\

Function: instance_array_types_match

  Inputs:

 Outputs:

 Purpose: True iff a connection of the given type connects to a
          port of the given type without splitting.

\*******************************************************************/

static std::optional<mp_integer> instance_array_vector_width(const typet &type)
{
  if(type.id() == ID_bool)
    return mp_integer{1};
  else if(
    type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
    type.id() == ID_verilog_unsignedbv || type.id() == ID_verilog_signedbv)
  {
    return string2integer(type.get_string(ID_width));
  }
  else
    return {};
}

static bool instance_array_types_match(const typet &a, const typet &b)
{
  if(
    a.id() == ID_array && b.id() == ID_array &&
    a.get(ID_C_verilog_type) == ID_verilog_unpacked_array &&
    b.get(ID_C_verilog_type) == ID_verilog_unpacked_array)
  {
    auto &array_a = to_verilog_array_type(a);
    auto &array_b = to_verilog_array_type(b);
    return array_a.size_int() == array_b.size_int() &&
           instance_array_types_match(
             array_a.element_type(), array_b.element_type());
  }

  auto width_a = instance_array_vector_width(a);
  auto width_b = instance_array_vector_width(b);

  return width_a.has_value() && width_b.has_value() && *width_a == *width_b;
}

/*******************************************************************\

Function: verilog_typecheckt::instance_array_element_connection

  Inputs:

 Outputs:

 Purpose: Given the (type-checked) connection of an instance
          array port, returns the connection for the element
          with the given index (0-based, in declaration order),
          per 1800-2017 23.3.3.

\*******************************************************************/

exprt verilog_typecheckt::instance_array_element_connection(
  const exprt &connection,
  const typet &port_type,
  const instance_array_dimst &dims,
  const mp_integer &number_of_elements,
  const mp_integer &element_index,
  const source_locationt &source_location)
{
  // 1800-2017 23.3.3: if the connection matches the port type,
  // it connects to every element of the array.
  if(instance_array_types_match(connection.type(), port_type))
    return connection;

  // Unpacked array connections are split element-wise
  // (1800-2017 23.3.3.5): the outermost dimensions of the
  // connection must match the dimensions of the instance array,
  // and the leftmost element of the connection connects to the
  // leftmost instance.
  if(connection.type().id() == ID_array)
  {
    exprt result = connection;
    mp_integer remaining = element_index;

    for(std::size_t d = 0; d < dims.size(); d++)
    {
      if(
        result.type().id() != ID_array ||
        result.type().get(ID_C_verilog_type) != ID_verilog_unpacked_array)
      {
        throw errort().with_location(source_location)
          << "instance array connection has too few unpacked dimensions";
      }

      auto &array_type = to_verilog_array_type(result.type());

      if(array_type.size_int() != dims[d].size())
      {
        throw errort().with_location(source_location)
          << "instance array connection dimension has size "
          << array_type.size_int() << ", but the instance array has size "
          << dims[d].size();
      }

      // the position within this dimension, 0-based from the left
      mp_integer stride = 1;
      for(std::size_t d2 = d + 1; d2 < dims.size(); d2++)
        stride *= dims[d2].size();

      mp_integer position = remaining / stride;
      remaining %= stride;

      // The leftmost element of the connection connects to the
      // leftmost instance.
      mp_integer verilog_index =
        array_type.increasing()
          ? array_type.offset() + position
          : array_type.offset() + array_type.size_int() - 1 - position;

      result =
        verilog_bit_select_exprt{
          std::move(result),
          from_integer(verilog_index, integer_typet{}),
          array_type.element_type()}
          .with_source_location(source_location);
    }

    if(!instance_array_types_match(result.type(), port_type))
    {
      throw errort().with_location(source_location)
        << "instance array connection element does not match the port type";
    }

    return result;
  }

  // Vector connections are split bit-wise (1800-2017 23.3.3):
  // the width of the connection must be the width of the port
  // times the number of elements, and the most significant bits
  // connect to the leftmost instance.
  auto port_width = instance_array_vector_width(port_type);
  auto connection_width = instance_array_vector_width(connection.type());

  if(
    port_width.has_value() && connection_width.has_value() &&
    *connection_width == *port_width * number_of_elements)
  {
    // The significance of the element's most significant bit,
    // 0-based from the least significant bit of the connection.
    mp_integer msb_position =
      *connection_width - 1 - element_index * *port_width;

    // Map bit significance to a Verilog index, honouring the
    // declared range of the connection, if any.
    const mp_integer offset =
      string2integer(connection.type().get_string(ID_C_offset));
    const bool increasing = connection.type().get_bool(ID_C_increasing);

    auto verilog_index = [&](const mp_integer &significance)
    {
      return increasing ? offset + *connection_width - 1 - significance
                        : offset + significance;
    };

    if(*port_width == 1)
    {
      return verilog_bit_select_exprt{
        connection,
        from_integer(verilog_index(msb_position), integer_typet{}),
        bool_typet{}}
        .with_source_location(source_location);
    }
    else
    {
      mp_integer index1 = verilog_index(msb_position);
      mp_integer index2 = verilog_index(msb_position - *port_width + 1);

      if(index1 < index2)
        std::swap(index1, index2); // now index1 >= index2

      // Part-select expressions are unsigned.
      return verilog_non_indexed_part_select_exprt{
        connection,
        from_integer(index1, integer_typet{}),
        from_integer(index2, integer_typet{}),
        unsignedbv_typet{numeric_cast_v<std::size_t>(*port_width)}}
        .with_source_location(source_location);
    }
  }

  throw errort().with_location(source_location)
    << "cannot split the connection over the " << number_of_elements
    << " elements of the instance array";
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
