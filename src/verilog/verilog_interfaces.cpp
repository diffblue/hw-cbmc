/*******************************************************************\

Module: Verilog Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>

#include <util/ebmc_util.h>
#include <util/mathematical_types.h>
#include <util/std_types.h>

#include "verilog_typecheck.h"
#include "verilog_expr.h"
#include "verilog_types.h"

/*******************************************************************\

Function: verilog_typecheckt::module_interface

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::check_module_ports(
  const verilog_module_sourcet &module_source)
{
  auto &module_ports = module_source.ports();
  auto &ports = to_module_type(module_symbol().type).ports();
  ports.clear();
  ports.reserve(module_ports.size());
  std::set<irep_idt> port_names;

  for(auto &decl : module_ports)
  {
    DATA_INVARIANT(decl.id() == ID_decl, "port declaration id");
    DATA_INVARIANT(
      decl.declarators().size() == 1,
      "port declarations must have one declarator");

    const auto &declarator = decl.declarators().front();

    const irep_idt &base_name = declarator.base_name();

    if(base_name.empty())
    {
      throw errort().with_location(decl.source_location())
        << "empty port name (module " << module_symbol().base_name << ')';
    }

    if(port_names.find(base_name) != port_names.end())
    {
      throw errort().with_location(declarator.source_location())
        << "duplicate port name: `" << base_name << '\'';
    }

    irep_idt identifier = hierarchical_identifier(base_name);

    const symbolt *port_symbol=0;

    // find the symbol

    if(ns.lookup(identifier, port_symbol))
    {
      throw errort().with_location(declarator.source_location())
        << "port `" << base_name << "' not declared";
    }

    irep_idt direction = decl.get_class();

    if(direction.empty())
    {
      if(!port_symbol->is_input && !port_symbol->is_output)
      {
        throw errort().with_location(declarator.source_location())
          << "port `" << base_name << "' not declared as input or output";
      }
      else if(port_symbol->is_input && !port_symbol->is_output)
        direction = ID_input;
      else if(!port_symbol->is_input && port_symbol->is_output)
        direction = ID_output;
      else
        direction = ID_inout;
    }
    else if(direction == ID_output_register)
    {
      direction = ID_output;
    }

    ports.emplace_back(identifier, base_name, port_symbol->type, direction);

    ports.back().set(ID_C_source_location, declarator.source_location());

    port_names.insert(base_name);
  }

  DATA_INVARIANT(ports.size() == module_ports.size(), "number of ports");

  // The variables and nets of the interfaces of the interface ports are
  // ports as well, which are connected to the members of the bound
  // interface instances, see connect_interface_members.
  for(std::size_t i = 0; i < module_ports.size(); i++)
  {
    // copy, as the vector may grow
    auto port_identifier = ports[i].identifier();
    auto port_type = ports[i].type();

    std::vector<const symbolt *> members;
    interface_members(port_identifier, port_type, members);

    for(auto member : members)
    {
      // e.g., bus.data, or bus[1].data
      auto suffix =
        id2string(member->name).substr(id2string(port_identifier).size());
      auto base_name = id2string(ports[i].base_name()) + suffix;
      auto source_location = ports[i].source_location();

      ports.emplace_back(member->name, base_name, member->type, ID_verilog_ref);
      ports.back().interface_port(port_identifier);
      ports.back().set(ID_C_source_location, source_location);
    }
  }

  // Check that input/output declarations are in the port list.
  for(auto &item : module_source.items())
  {
    if(item.id() == ID_decl)
    {
      auto &decl = to_verilog_decl(item);
      auto decl_class = decl.get_class();

      if(
        decl_class == ID_input || decl_class == ID_output ||
        decl_class == ID_output_register || decl_class == ID_inout ||
        decl_class == ID_verilog_no_direction)
      {
        for(auto &declarator : decl.declarators())
        {
          auto base_name = declarator.base_name();

          if(port_names.find(base_name) == port_names.end())
          {
            throw errort().with_location(declarator.source_location())
              << "port `" << base_name << "' not in port list";
          }
        }
      }
    }
  }
}

/*******************************************************************\

Function: interface_array_elements

  Inputs: an array of interface instances or of interface ports

 Outputs: its elements, in the order of the range, i.e., starting
          from the left index

 Purpose: The elements of an array of interface instances or of an
          array of interface ports, 1800-2017 25.4, are symbols of
          their own, named id[0], id[1], and so on.

\*******************************************************************/

static exprt::operandst interface_array_elements(const symbol_exprt &array)
{
  auto &array_type = to_verilog_array_type(array.type());
  auto size = array_type.size_int();
  auto offset = array_type.offset();
  exprt::operandst result;

  for(mp_integer i = 0; i < size; ++i)
  {
    auto index = array_type.increasing() ? offset + i : offset + size - 1 - i;
    result.push_back(symbol_exprt{
      id2string(array.get_identifier()) + '[' + integer2string(index) + ']',
      array_type.element_type()});
  }

  return result;
}

/*******************************************************************\

Function: verilog_typecheckt::interface_port_actual

  Inputs:

 Outputs:

 Purpose: The interface instance (or array of interface instances)
          that the given port connection expression denotes, as a
          symbol expression, or nil if the expression is not the
          name of an interface instance. Elements of arrays of interface
          instances are resolved to their symbols, and assignment
          patterns, which bind arrays of interface ports, are resolved
          element-wise.

\*******************************************************************/

exprt verilog_typecheckt::interface_port_actual(const exprt &expr)
{
  if(expr.id() == ID_verilog_identifier)
  {
    auto *symbol = resolve(to_verilog_identifier_expr(expr).base_name());

    if(symbol == nullptr)
      return nil_exprt{};

    if(
      symbol->type.id() != ID_verilog_module_instance &&
      !is_interface_array_type(symbol->type))
    {
      return nil_exprt{};
    }

    return symbol->symbol_expr();
  }
  else if(expr.id() == ID_verilog_bit_select)
  {
    // An element of an array of interface instances, 1800-2017 25.4,
    // which is a symbol of its own, e.g., bus[1].
    auto bit_select = to_verilog_bit_select_expr(expr);
    bit_select.src() = interface_port_actual(bit_select.src());

    if(
      bit_select.src().id() != ID_symbol ||
      !is_interface_array_type(bit_select.src().type()))
    {
      return nil_exprt{};
    }

    return convert_interface_array_element(std::move(bit_select));
  }
  else if(expr.id() == ID_verilog_assignment_pattern)
  {
    exprt result = expr;

    for(auto &op : result.operands())
    {
      op = interface_port_actual(op);
      if(op.is_nil())
        return nil_exprt{};
    }

    return result;
  }
  else
    return nil_exprt{};
}

/*******************************************************************\

Function: verilog_typecheckt::interface_port_actuals

  Inputs:

 Outputs:

 Purpose: The interface instances that the given instance binds to
          the interface ports of the given design element, by port base
          name, as far as they can be determined from the port
          connections.

\*******************************************************************/

std::map<irep_idt, exprt> verilog_typecheckt::interface_port_actuals(
  const irep_idt &module_identifier,
  const verilog_instt::instancet &instance)
{
  std::map<irep_idt, exprt> result;

  auto source_it =
    symbol_table.symbols.find(id2string(module_identifier) + "$source");

  if(source_it == symbol_table.symbols.end())
    return result; // error is raised by instantiate_design_element

  const auto &module_source =
    to_verilog_module_source(source_it->second.type.find(ID_module_source));

  auto &ports = module_source.ports();

  if(instance.named_port_connections())
  {
    for(auto &connection : instance.connections())
    {
      if(connection.id() != ID_verilog_named_port_connection)
        continue; // e.g., a wildcard connection

      auto &named_connection = to_verilog_named_port_connection(connection);

      if(named_connection.port().id() != ID_verilog_identifier)
        continue;

      auto actual = interface_port_actual(named_connection.value());

      if(actual.is_not_nil())
      {
        auto &port_base_name =
          to_verilog_identifier_expr(named_connection.port()).base_name();
        result[port_base_name] = std::move(actual);
      }
    }
  }
  else
  {
    auto &connections = instance.connections();

    for(std::size_t i = 0; i < connections.size() && i < ports.size(); i++)
    {
      auto actual = interface_port_actual(connections[i]);

      if(actual.is_not_nil())
      {
        auto &port_base_name = ports[i].declarators().front().base_name();
        result[port_base_name] = std::move(actual);
      }
    }
  }

  return result;
}

/*******************************************************************\

Function: verilog_typecheckt::interface_port_assignments

  Inputs:

 Outputs:

 Purpose: The parameter assignments of the interface ports of the given
          design element for the given instance: for each interface
          port that the instance binds to an interface instance, the
          interface type of that instance, i.e., its parameter
          assignments, including those of its own interface ports, and
          its defparams. These are passed to instantiate_design_element
          with the parameter assignments of the design element.

\*******************************************************************/

exprt::operandst verilog_typecheckt::interface_port_assignments(
  const irep_idt &module_identifier,
  const verilog_instt::instancet &instance)
{
  exprt::operandst result;

  for(auto &[port, actual] :
      interface_port_actuals(module_identifier, instance))
  {
    auto interface_type = interface_type_of_actual(actual);

    if(interface_type.is_nil())
      continue;

    exprt assignment{ID_verilog_interface_port_assignment};
    assignment.set(ID_parameter, port);
    assignment.add(ID_value) = std::move(interface_type);
    result.push_back(std::move(assignment));
  }

  return result;
}

/*******************************************************************\

Function: verilog_typecheckt::interface_type_of_actual

  Inputs:

 Outputs:

 Purpose: The interface type of the given actual of an interface port,
          see interface_port_actual: the instantiation recorded on the
          interface instance, or, for an array of interfaces, the list
          of the interface types of the elements, in the order of the
          range, as the elements are bound pairwise. Nil if unknown.

\*******************************************************************/

irept verilog_typecheckt::interface_type_of_actual(const exprt &actual) const
{
  if(actual.id() == ID_symbol)
  {
    auto &identifier = to_symbol_expr(actual).get_identifier();

    if(is_interface_array_type(actual.type()))
    {
      irept result{ID_verilog_assignment_pattern};

      for(auto &element : interface_array_elements(to_symbol_expr(actual)))
        result.get_sub().push_back(interface_type_of_actual(element));

      return result;
    }

    auto record = get_instantiation_record(identifier);
    return record.has_value() ? *record : irept{ID_nil};
  }
  else if(actual.id() == ID_verilog_assignment_pattern)
  {
    irept result{ID_verilog_assignment_pattern};

    for(auto &op : actual.operands())
      result.get_sub().push_back(interface_type_of_actual(op));

    return result;
  }
  else
    return irept{ID_nil};
}

/*******************************************************************\

Function: verilog_typecheckt::instantiation_record

  Inputs:

 Outputs:

 Purpose: The irep form of an instantiation

\*******************************************************************/

irept verilog_typecheckt::instantiation_record(
  const verilog_instantiationt &instantiation)
{
  irept record{ID_verilog_instantiation};

  auto &parameter_assignments =
    static_cast<exprt &>(record.add(ID_parameter_assignments));
  parameter_assignments.operands() = instantiation.parameter_assignments;

  auto &defparams = record.add(ID_verilog_defparams);
  for(auto &[name, value] : instantiation.defparams)
    defparams.add(name) = value;

  return record;
}

/*******************************************************************\

Function: verilog_typecheckt::instantiation_of_record

  Inputs:

 Outputs:

 Purpose: The instantiation in the given irep form

\*******************************************************************/

auto verilog_typecheckt::instantiation_of_record(const irept &record)
  -> verilog_instantiationt
{
  verilog_instantiationt result;

  result.parameter_assignments =
    static_cast<const exprt &>(record.find(ID_parameter_assignments))
      .operands();

  for(auto &[name, value] : record.find(ID_verilog_defparams).get_named_sub())
    result.defparams[name] = static_cast<const exprt &>(value);

  return result;
}

/*******************************************************************\

Function: verilog_typecheckt::set_instantiation

  Inputs:

 Outputs:

 Purpose: Record on the given symbol of an interface instance or an
          interface port how the interface is instantiated.

\*******************************************************************/

void verilog_typecheckt::set_instantiation(
  symbolt &symbol,
  const verilog_instantiationt &instantiation)
{
  symbol.value.add(ID_verilog_instantiation) =
    instantiation_record(instantiation);
}

/*******************************************************************\

Function: verilog_typecheckt::get_instantiation_record

  Inputs:

 Outputs:

 Purpose: How the interface instance or interface port with the given
          identifier is instantiated, if recorded.

\*******************************************************************/

std::optional<irept> verilog_typecheckt::get_instantiation_record(
  const irep_idt &instance_identifier) const
{
  const symbolt *symbol;
  if(ns.lookup(instance_identifier, symbol))
    return {};

  const irept &record = symbol->value.find(ID_verilog_instantiation);

  if(record.is_nil())
    return {};

  return record;
}

/*******************************************************************\

Function: verilog_typecheckt::instantiate_interface_ports

  Inputs:

 Outputs:

 Purpose: Instantiate the interface of each interface port of the given
          port declaration under the port's identifier, so that
          hierarchical member access (e.g., bus.i) works. Arrays of
          interface ports, 1800-2017 25.4, yield one instance per array
          element, named bus[0], bus[1], ... The interface type of a
          port, i.e., the parameters of the interface, are those that
          the instantiation of the design element gives, see
          set_interface_port_types.

          This is done as soon as the symbols of the ports exist, i.e.,
          when the port declaration is elaborated, so that the members
          may be used in elaboration-time constants, e.g., $bits(bus.i).
          Declarations of ports that are not interface ports are
          ignored.

\*******************************************************************/

void verilog_typecheckt::instantiate_interface_ports(const verilog_declt &decl)
{
  for(auto &declarator : decl.declarators())
  {
    const irep_idt &base_name = declarator.base_name();
    irep_idt port_identifier = hierarchical_identifier(base_name);

    const symbolt *port_symbol;
    if(ns.lookup(port_identifier, port_symbol))
      continue;

    // Is this an interface port, or an array thereof? Arrays of interface
    // ports may have any number of dimensions.
    auto *type = &port_symbol->type;
    while(type->id() == ID_array)
      type = &to_array_type(*type).element_type();

    if(type->id() != ID_verilog_module_instance)
      continue;

    irep_idt interface_base_name = type->get(ID_base_name);
    if(interface_base_name.empty())
      continue;

    // Find the interface source, to be instantiated under the port.
    irep_idt interface_module_id = verilog_module_symbol(interface_base_name);

    auto &location = port_symbol->location.is_nil()
                       ? declarator.source_location()
                       : port_symbol->location;

    // The interface type, which is the same for all dimensions.
    irept interface_type = type->find(ID_C_verilog_interface_type);

    instantiate_interface_port(
      port_symbol->type,
      location,
      interface_module_id,
      interface_base_name,
      base_name,
      port_identifier,
      interface_type);
  }
}

/*******************************************************************\

Function: verilog_typecheckt::instantiate_interface_port

  Inputs:

 Outputs:

 Purpose: Instantiate the given interface under the given identifier,
          with the given interface type, i.e., the instantiation of the
          interface instance that is bound to the port, or nil for the
          defaults. When the type is an array, this recurses into the
          array elements, which are given the identifiers id[0],
          id[1], ..., and the interface type is a list with one entry
          per element.

\*******************************************************************/

void verilog_typecheckt::instantiate_interface_port(
  const typet &type,
  const source_locationt &location,
  const irep_idt &interface_module_id,
  const irep_idt &interface_base_name,
  const irep_idt &base_name,
  const irep_idt &identifier,
  const irept &interface_type)
{
  if(type.id() == ID_array)
  {
    // An array of interface ports, 1800-2017 25.4. Each element is
    // instantiated separately. The elements are given the indices that
    // the array's declared range yields.
    auto &array_type = to_verilog_array_type(type);
    auto size = array_type.size_int();
    auto offset = array_type.offset();

    // the interface types of the elements, in the order of the range
    const bool have_element_types =
      interface_type.id() == ID_verilog_assignment_pattern &&
      interface_type.get_sub().size() == size;

    for(mp_integer i = 0; i < size; ++i)
    {
      // The elements are stored starting from the left index of the range.
      auto index = array_type.increasing() ? offset + i : offset + size - 1 - i;
      auto suffix = '[' + integer2string(index) + ']';

      symbolt element_symbol{
        id2string(identifier) + suffix, array_type.element_type(), mode};

      element_symbol.module = verilog_root_module_identifier();
      element_symbol.base_name = id2string(base_name) + suffix;
      element_symbol.pretty_name =
        strip_verilog_root_prefix(element_symbol.name);
      element_symbol.location = location;
      element_symbol.value.make_nil();

      auto element_base_name = element_symbol.base_name;
      auto element_identifier = element_symbol.name;
      add_symbol(std::move(element_symbol));

      const irept &element_interface_type =
        have_element_types
          ? interface_type.get_sub()[numeric_cast_v<std::size_t>(i)]
          : get_nil_irep();

      // recursive call, for further dimensions
      instantiate_interface_port(
        array_type.element_type(),
        location,
        interface_module_id,
        interface_base_name,
        element_base_name,
        element_identifier,
        element_interface_type);
    }

    return;
  }

  // The interface under the port is instantiated as the interface
  // instance that is bound to the port, i.e., with the same parameter
  // assignments, including those of its interface ports, and the same
  // defparams. Without a bound instance, e.g., for the ports of a
  // top-level module, the defaults are used.
  verilog_instantiationt instantiation;

  if(interface_type.id() == ID_verilog_instantiation)
    instantiation = instantiation_of_record(interface_type);

  instantiate_design_element(
    location,
    interface_module_id,
    interface_base_name,
    identifier,
    instantiation.parameter_assignments,
    instantiation.defparams);

  // Update the instance symbol value to record the interface binding, and
  // the interface type, for interface ports of submodules that this port
  // is bound to.
  symbolt &symbol = symbol_table_lookup(identifier);
  symbol.value = verilog_module_instancet{id2string(identifier) + "$module"};
  set_instantiation(symbol, instantiation);
}

/*******************************************************************\

Function: verilog_typecheckt::interface_members

  Inputs: the identifier and type of an interface port, or of an
          interface instance

 Outputs: the variables and nets of the interfaces instantiated under
          the port, in the order of their identifiers

 Purpose: These include the members of the elements of an array of
          interface ports, 1800-2017 25.4, and those of interface
          instances within the interfaces, e.g., under their interface
          ports.

\*******************************************************************/

void verilog_typecheckt::interface_members(
  const irep_idt &identifier,
  const typet &type,
  std::vector<const symbolt *> &dest) const
{
  if(is_interface_array_type(type))
  {
    for(auto &element :
        interface_array_elements(symbol_exprt{identifier, type}))
    {
      interface_members(
        to_symbol_expr(element).get_identifier(), element.type(), dest);
    }

    return;
  }

  if(type.id() != ID_verilog_module_instance)
    return;

  // The members are the symbols with the identifier of the instance as
  // prefix. The elements of arrays of interface instances are reached
  // through their arrays.
  auto prefix = id2string(identifier) + '.';
  std::vector<const symbolt *> members;

  for(auto &[name, symbol] : symbol_table.symbols)
  {
    auto &name_string = id2string(name);

    if(
      name_string.size() > prefix.size() &&
      name_string.compare(0, prefix.size(), prefix) == 0 &&
      name_string.find_first_of(".[", prefix.size()) == std::string::npos)
    {
      members.push_back(&symbol);
    }
  }

  std::sort(
    members.begin(),
    members.end(),
    [](const symbolt *a, const symbolt *b)
    { return id2string(a->name) < id2string(b->name); });

  for(auto member : members)
  {
    if(
      member->type.id() == ID_verilog_module_instance ||
      is_interface_array_type(member->type))
    {
      interface_members(member->name, member->type, dest);
    }
    else if(
      !member->is_type && !member->is_macro && !member->is_property &&
      member->type.id() != ID_code && member->type.id() != ID_named_block &&
      member->type.id() != ID_module && member->type.id() != ID_verilog_genvar)
    {
      dest.push_back(member);
    }
  }
}

/*******************************************************************\

Function: verilog_typecheckt::connect_interface_members

  Inputs: the connections of an instance, and the type of the
          instantiated design element

 Outputs:

 Purpose: The ports for the variables and nets of the interfaces of the
          interface ports, see check_module_ports, are connected to the
          corresponding members of the interface instances that the
          interface ports are bound to. The connections are converted to
          named connections if need be.

\*******************************************************************/

void verilog_typecheckt::connect_interface_members(
  exprt::operandst &connections,
  const module_typet &module_type)
{
  auto &ports = module_type.ports();

  // the member ports, by interface port
  std::map<irep_idt, std::vector<const module_typet::portt *>> members;

  for(auto &port : ports)
    if(port.is_interface_member())
      members[port.interface_port()].push_back(&port);

  if(members.empty())
    return;

  // Positional connections are converted to named ones.
  if(
    !connections.empty() &&
    connections.front().id() != ID_verilog_named_port_connection)
  {
    for(std::size_t i = 0; i < connections.size(); i++)
    {
      auto &port = ports[i];
      auto source_location = connections[i].source_location();
      connections[i] = verilog_inst_baset::named_port_connectiont{
        symbol_exprt{port.identifier(), port.type()}.with_source_location(
          source_location),
        std::move(connections[i])};
    }
  }

  exprt::operandst member_connections;

  for(auto &connection : connections)
  {
    auto &named_connection = to_verilog_named_port_connection(connection);
    auto &port = to_symbol_expr(named_connection.port());
    auto members_it = members.find(port.get_identifier());

    if(members_it != members.end() && named_connection.value().is_not_nil())
    {
      connect_interface_members(
        port, named_connection.value(), members_it->second, member_connections);
    }
  }

  for(auto &connection : member_connections)
    connections.push_back(std::move(connection));
}

/*******************************************************************\

Function: verilog_typecheckt::connect_interface_members

  Inputs: an interface port, or an element of an array of these, its
          actual, and the member ports of the interface port

 Outputs: the connections of the member ports of the given port, or
          element, to the corresponding members of the actual

 Purpose: The elements of an array of interface ports are bound to the
          elements of the actual pairwise, in the order of the ranges.
          The actual is then an array of interface instances, or an
          assignment pattern of these.

\*******************************************************************/

void verilog_typecheckt::connect_interface_members(
  const symbol_exprt &port,
  const exprt &actual,
  const std::vector<const module_typet::portt *> &members,
  exprt::operandst &dest) const
{
  if(is_interface_array_type(port.type()))
  {
    exprt::operandst actual_elements;

    if(actual.id() == ID_verilog_assignment_pattern)
      actual_elements = actual.operands();
    else if(actual.id() == ID_symbol && is_interface_array_type(actual.type()))
      actual_elements = interface_array_elements(to_symbol_expr(actual));

    auto port_elements = interface_array_elements(port);

    for(std::size_t i = 0;
        i < port_elements.size() && i < actual_elements.size();
        i++)
    {
      connect_interface_members(
        to_symbol_expr(port_elements[i]), actual_elements[i], members, dest);
    }

    return;
  }

  if(actual.id() != ID_symbol)
    return;

  // The members of the port are those of its interface, and the actual
  // is an instance of the same interface, with the same members.
  auto prefix = id2string(port.get_identifier()) + '.';
  auto &actual_identifier = id2string(to_symbol_expr(actual).get_identifier());

  for(auto member : members)
  {
    auto &member_identifier = id2string(member->identifier());

    if(member_identifier.compare(0, prefix.size(), prefix) != 0)
      continue;

    auto actual_member_identifier =
      actual_identifier + '.' + member_identifier.substr(prefix.size());

    const symbolt *actual_member;
    if(ns.lookup(actual_member_identifier, actual_member))
      continue;

    // The interface under the port must be instantiated with the
    // parameters of the bound instance for the types to match.
    if(member->type() != actual_member->type)
    {
      throw errort().with_location(actual.source_location())
        << "interface port `" << strip_verilog_root_prefix(member->identifier())
        << "' is bound to `" << actual_member->display_name()
        << "', which has a different type";
    }

    dest.push_back(verilog_inst_baset::named_port_connectiont{
      symbol_exprt{member->identifier(), member->type()}.with_source_location(
        actual.source_location()),
      actual_member->symbol_expr().with_source_location(
        actual.source_location())});
  }
}

/*******************************************************************\

Function: verilog_typecheckt::interface_generate_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::interface_generate_block(
  const verilog_generate_blockt &generate_block)
{
  // These introduce scope, much like a named block statement.
  bool is_named = generate_block.is_named();

  if(is_named)
  {
    irep_idt base_name = generate_block.base_name();

    // 1800-2017 27.6: the name of a generate block is part of the
    // hierarchy, and hence must be visible to hierarchical identifiers.
    add_named_block_symbol(base_name, generate_block.source_location());

    enter_named_block(base_name);
  }

  for(auto &item : generate_block.module_items())
    interface_module_item(item);

  if(is_named)
    named_blocks.pop_back();
}

/*******************************************************************\

Function: verilog_typecheckt::interface_module_item

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::interface_module_item(
  const verilog_module_itemt &module_item)
{
  if(module_item.id()==ID_decl)
  {
  }
  else if(module_item.id() == ID_verilog_genvar_decl)
  {
  }
  else if(module_item.id()==ID_parameter_decl ||
          module_item.id()==ID_local_parameter_decl)
  {
    // already done by elaborate_parameters
  }
  else if(module_item.id() == ID_inst)
  {
  }
  else if(module_item.id() == ID_inst_builtin)
  {
  }
  else if(
    module_item.id() == ID_verilog_always ||
    module_item.id() == ID_verilog_always_comb ||
    module_item.id() == ID_verilog_always_ff ||
    module_item.id() == ID_verilog_always_latch)
    interface_statement(to_verilog_always_base(module_item).statement());
  else if(module_item.id()==ID_initial)
    interface_statement(to_verilog_initial(module_item).statement());
  else if(module_item.id()==ID_generate_block)
    interface_generate_block(to_verilog_generate_block(module_item));
  else if(module_item.id() == ID_set_genvars)
    interface_module_item(to_verilog_set_genvars(module_item).module_item());
  else if(
    module_item.id() == ID_verilog_assert_property ||
    module_item.id() == ID_verilog_assume_property ||
    module_item.id() == ID_verilog_restrict_property ||
    module_item.id() == ID_verilog_cover_property ||
    module_item.id() == ID_verilog_cover_sequence)
  {
    // done later
  }
  else if(module_item.id() == ID_verilog_assertion_item)
  {
  }
  else if(
    module_item.id() == ID_continuous_assign ||
    module_item.id() == ID_parameter_override)
  {
    // does not yield symbol
  }
  else if(module_item.id() == ID_verilog_final)
  {
  }
  else if(module_item.id() == ID_verilog_let)
  {
    // already done during constant elaboration
  }
  else if(module_item.id() == ID_verilog_empty_item)
  {
  }
  else if(module_item.id() == ID_verilog_class)
  {
  }
  else if(module_item.id() == ID_verilog_smv_using)
  {
  }
  else if(module_item.id() == ID_verilog_smv_assume)
  {
  }
  else if(module_item.id() == ID_verilog_package_import)
  {
  }
  else if(module_item.id() == ID_verilog_clocking)
  {
  }
  else if(module_item.id() == ID_verilog_covergroup)
  {
  }
  else if(module_item.id() == ID_verilog_default_clocking)
  {
  }
  else if(module_item.id() == ID_verilog_default_disable)
  {
  }
  else if(module_item.id() == ID_verilog_property_declaration)
  {
  }
  else if(module_item.id() == ID_verilog_sequence_declaration)
  {
  }
  else if(module_item.id() == ID_function_call)
  {
  }
  else if(module_item.id() == ID_verilog_timeunit)
  {
  }
  else if(module_item.id() == ID_verilog_timeprecision)
  {
  }
  else if(module_item.id() == ID_verilog_specparam_decl)
  {
  }
  else if(module_item.id() == ID_specify)
  {
    // 1800-2017 A.7.1: specify block; contributes no module interface.
  }
  else if(module_item.id() == ID_verilog_modport_declaration)
  {
  }
  else if(module_item.id() == ID_verilog_interface)
  {
    // nested interface, 1800-2017 25.3
  }
  else if(module_item.id() == ID_verilog_checker)
  {
    // A checker declared inside a module (1800-2017 17.3) is
    // registered as a separate module source during collect_symbols;
    // it yields no symbol in the containing module's interface.
  }
  else
  {
    DATA_INVARIANT(false, "unexpected module item: " + module_item.id_string());
  }
}

/*******************************************************************\

Function: verilog_typecheckt::interface_statement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::interface_statement(
  const verilog_statementt &statement)
{
  if(statement.id()==ID_block)
    interface_block(to_verilog_block(statement));
  else if(
    statement.id() == ID_verilog_case || statement.id() == ID_verilog_casex ||
    statement.id() == ID_verilog_casez)
  {
  }
  else if(statement.id()==ID_if)
  {
  }
  else if(statement.id()==ID_decl)
  {
  }
  else if(statement.id()==ID_event_guard)
  {
    if(statement.operands().size()!=2)
    {
      throw errort().with_location(statement.source_location())
        << "event_guard expected to have two operands";
    }

    interface_statement(
      to_verilog_event_guard(statement).body());
  }
  else if(statement.id()==ID_delay)
  {
    if(statement.operands().size()!=2)
    {
      throw errort().with_location(statement.source_location())
        << "delay expected to have two operands";
    }

    interface_statement(
      to_verilog_delay(statement).body());
  }
  else if(statement.id()==ID_for)
  {
  }
  else if(statement.id()==ID_while)
  {
  }
  else if(statement.id()==ID_repeat)
  {
  }
  else if(statement.id()==ID_forever)
  {
  }
}

/*******************************************************************\

Function: verilog_typecheckt::add_named_block_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::add_named_block_symbol(
  const irep_idt &base_name,
  const source_locationt &source_location)
{
  symbolt symbol{
    hierarchical_identifier(base_name), typet{ID_named_block}, mode};

  symbol.base_name = base_name;
  symbol.module = module_identifier;
  symbol.pretty_name = strip_verilog_root_prefix(symbol.name);
  symbol.location = source_location;

  if(symbol_table.add(symbol))
  {
    throw errort().with_location(source_location)
      << "duplicate definition of identifier `" << base_name << "' in module `"
      << module_symbol().base_name << '\'';
  }
}

/*******************************************************************\

Function: verilog_typecheckt::interface_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::interface_block(const verilog_blockt &statement)
{
  if(statement.is_named())
    add_named_block_symbol(statement.base_name(), statement.source_location());

  enter_named_block(statement.block_id());

  // do decl
  const exprt &decl=static_cast<const exprt &>(
    statement.find("decl-brace"));

  forall_operands(it, decl)
    interface_module_item(
      static_cast<const verilog_module_itemt &>(*it));

  // do block itself

  for(auto &block_statement : statement.statements())
    interface_statement(block_statement);

  named_blocks.pop_back();
}
