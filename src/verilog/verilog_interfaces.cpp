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

Function: verilog_typecheckt::is_interface

  Inputs:

 Outputs:

 Purpose: True iff the design element with the given base name
          is an interface.

\*******************************************************************/

bool verilog_typecheckt::is_interface(const irep_idt &module_base_name) const
{
  auto source_identifier =
    id2string(verilog_module_symbol(module_base_name)) + "$source";

  const symbolt *source_symbol;
  if(ns.lookup(source_identifier, source_symbol))
    return false;

  return source_symbol->type.find(ID_module_source).id() ==
         ID_verilog_interface;
}

/*******************************************************************\

Function: verilog_typecheckt::interface_port_actual

  Inputs:

 Outputs:

 Purpose: The interface instance (or array of interface instances)
          that the given port connection expression denotes, as a
          symbol expression, or nil if the expression is not the
          name of an interface instance. Assignment patterns,
          which bind arrays of interface ports, are resolved
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
          the interface ports of the given module, by port base
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
    return result; // error is raised by instantiate_module

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

Function: verilog_typecheckt::interface_parameter_assignments

  Inputs:

 Outputs:

 Purpose: The parameter values of the given interface instance, as
          named parameter assignments for the interface with the
          given identifier. The interface instance is expected to
          have been elaborated already.

\*******************************************************************/

exprt::operandst verilog_typecheckt::interface_parameter_assignments(
  const irep_idt &interface_module_id,
  const irep_idt &actual_identifier)
{
  exprt::operandst result;

  auto source_it =
    symbol_table.symbols.find(id2string(interface_module_id) + "$source");

  if(source_it == symbol_table.symbols.end())
    return result;

  const auto &interface_source =
    to_verilog_module_source(source_it->second.type.find(ID_module_source));

  for(auto &declarator : get_parameter_declarators(interface_source))
  {
    auto &base_name = declarator.base_name();

    const symbolt *parameter_symbol;
    if(ns.lookup(
         id2string(actual_identifier) + '.' + id2string(base_name),
         parameter_symbol))
    {
      continue; // not (yet) known, use the default
    }

    exprt value;

    if(parameter_symbol->is_type)
      value = type_exprt{parameter_symbol->type};
    else if(parameter_symbol->value.is_not_nil())
      value = parameter_symbol->value;
    else
      continue;

    exprt assignment{ID_named_parameter_assignment};
    assignment.set(ID_parameter, base_name);
    assignment.add(ID_value) = std::move(value);
    assignment.add_source_location() = declarator.source_location();
    result.push_back(std::move(assignment));
  }

  return result;
}

/*******************************************************************\

Function: verilog_typecheckt::instantiate_interface_ports

  Inputs:

 Outputs:

 Purpose: For each port that has an interface type, instantiate
          the interface under the port's identifier so that
          hierarchical member access (e.g., bus.i) works.
          Arrays of interface ports, 1800-2017 25.4, yield one
          instance per array element, named bus[0], bus[1], ...
          The interface is instantiated with the parameters of
          the interface instance that is bound to the port, when
          that instance is known.

\*******************************************************************/

void verilog_typecheckt::instantiate_interface_ports(
  const verilog_module_sourcet &module_source)
{
  for(auto &decl : module_source.ports())
  {
    DATA_INVARIANT(decl.id() == ID_decl, "port declaration id");

    const auto &declarator = decl.declarators().front();
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

    // The interface instance bound to the port, if known.
    auto actual_it = port_actuals.find(base_name);
    exprt actual =
      actual_it == port_actuals.end() ? exprt{nil_exprt{}} : actual_it->second;

    instantiate_interface_port(
      port_symbol->type,
      port_symbol->location,
      interface_module_id,
      interface_base_name,
      base_name,
      port_identifier,
      actual);
  }
}

/*******************************************************************\

Function: verilog_typecheckt::instantiate_interface_port

  Inputs:

 Outputs:

 Purpose: Instantiate the given interface under the given identifier,
          with the parameters of the given actual, which is the
          interface instance bound to the port, or nil if unknown.
          When the type is an array, this recurses into the array
          elements, which are given the identifiers id[0], id[1], ...

\*******************************************************************/

void verilog_typecheckt::instantiate_interface_port(
  const typet &type,
  const source_locationt &location,
  const irep_idt &interface_module_id,
  const irep_idt &interface_base_name,
  const irep_idt &base_name,
  const irep_idt &identifier,
  const exprt &actual)
{
  if(type.id() == ID_array)
  {
    // An array of interface ports, 1800-2017 25.4. Each element is
    // instantiated separately. The elements are given the indices that
    // the array's declared range yields.
    auto &array_type = to_verilog_array_type(type);
    auto size = array_type.size_int();
    auto offset = array_type.offset();

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

      // The actual for the element: the actual may be an assignment
      // pattern with one interface instance per element, or the name of
      // another array of interfaces. The elements are bound pairwise,
      // in the order of the two ranges.
      exprt element_actual = nil_exprt{};

      if(
        actual.id() == ID_verilog_assignment_pattern &&
        actual.operands().size() == size)
      {
        element_actual = actual.operands()[numeric_cast_v<std::size_t>(i)];
      }
      else if(
        actual.id() == ID_symbol && is_interface_array_type(actual.type()) &&
        to_verilog_array_type(actual.type()).size_int() == size)
      {
        auto &actual_type = to_verilog_array_type(actual.type());
        auto actual_offset = actual_type.offset();
        auto actual_index = actual_type.increasing()
                              ? actual_offset + i
                              : actual_offset + size - 1 - i;
        element_actual = symbol_exprt{
          id2string(to_symbol_expr(actual).get_identifier()) + '[' +
            integer2string(actual_index) + ']',
          actual_type.element_type()};
      }

      // recursive call, for further dimensions
      instantiate_interface_port(
        array_type.element_type(),
        location,
        interface_module_id,
        interface_base_name,
        element_base_name,
        element_identifier,
        element_actual);
    }

    return;
  }

  // The parameters of the port's interface are those of the interface
  // instance that is bound to the port.
  exprt::operandst parameters;

  if(actual.id() == ID_symbol)
  {
    parameters = interface_parameter_assignments(
      interface_module_id, to_symbol_expr(actual).get_identifier());
  }

  std::map<irep_idt, exprt> no_defparams;

  instantiate_module(
    location,
    interface_module_id,
    interface_base_name,
    identifier,
    parameters,
    no_defparams);

  // Update the instance symbol value to record the module binding
  symbolt &symbol = symbol_table_lookup(identifier);
  symbol.value = verilog_module_instancet{id2string(identifier) + "$module"};

  // The members of the interface under the port are the members of the
  // bound interface instance.
  if(actual.id() == ID_symbol)
    alias_interface_port_members(
      identifier, to_symbol_expr(actual).get_identifier(), location);
}

/*******************************************************************\

Function: verilog_typecheckt::alias_interface_port_members

  Inputs:

 Outputs:

 Purpose: An interface port is a reference to the bound interface
          instance, 1800-2017 25.3. The variables and nets of the
          interface that is instantiated under the port are hence
          the variables and nets of the bound instance. These are
          made aliases, i.e., macros whose value is the member of
          the bound instance, so that reads and writes through the
          port are reads and writes of the bound instance's member.

\*******************************************************************/

void verilog_typecheckt::alias_interface_port_members(
  const irep_idt &port_identifier,
  const irep_idt &bound_instance_identifier,
  const source_locationt &location)
{
  auto port_prefix = id2string(port_identifier) + '.';
  auto bound_prefix = id2string(bound_instance_identifier) + '.';

  // The symbol table is modified while iterating; collect first.
  std::vector<irep_idt> members;

  for(auto &entry : symbol_table.symbols)
  {
    auto &id = id2string(entry.first);

    // direct members only; nested scopes have their own symbols
    if(
      id.size() <= port_prefix.size() ||
      id.compare(0, port_prefix.size(), port_prefix) != 0 ||
      id.find('.', port_prefix.size()) != std::string::npos)
    {
      continue;
    }

    auto &member_symbol = entry.second;

    // variables and nets only
    if(
      member_symbol.is_type || member_symbol.is_macro ||
      member_symbol.is_property ||
      member_symbol.type.id() == ID_verilog_module_instance ||
      member_symbol.type.id() == ID_code ||
      member_symbol.type.id() == ID_named_block ||
      member_symbol.type.id() == ID_module ||
      member_symbol.type.id() == ID_verilog_genvar)
    {
      continue;
    }

    members.push_back(entry.first);
  }

  for(auto &member : members)
  {
    auto member_name = id2string(member).substr(port_prefix.size());
    auto bound_id = bound_prefix + member_name;

    const symbolt *bound_symbol;
    if(ns.lookup(bound_id, bound_symbol))
      continue; // e.g., a member of a modport that is not in the interface

    symbolt &member_symbol = symbol_table_lookup(member);

    // The interface under the port is instantiated with the parameters
    // of the bound instance, and hence the types are expected to match.
    if(member_symbol.type != bound_symbol->type)
    {
      throw errort().with_location(location)
        << "interface port `" << member_symbol.display_name()
        << "' is bound to `" << bound_symbol->display_name()
        << "', which has a different type";
    }

    member_symbol.is_macro = true;
    member_symbol.value = bound_symbol->symbol_expr();
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

Function: verilog_typecheckt::interface_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::interface_block(
  const verilog_blockt &statement)
{
  if(statement.is_named())
  {
    const irep_idt base_name = statement.base_name();

    // need to add to symbol table
    symbolt symbol;

    symbol.mode=mode;
    symbol.base_name = base_name;
    symbol.type=typet(ID_named_block);
    symbol.module=module_identifier;
    symbol.name = hierarchical_identifier(symbol.base_name);
    symbol.pretty_name = strip_verilog_root_prefix(symbol.name);
    symbol.value=nil_exprt();

    if(symbol_table.add(symbol))
    {
      throw errort().with_location(statement.source_location())
        << "duplicate definition of identifier `" << symbol.base_name
        << "' in module `" << module_symbol().base_name << '\'';
    }
  }

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
