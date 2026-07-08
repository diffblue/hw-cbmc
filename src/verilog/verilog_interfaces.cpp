/*******************************************************************\

Module: Verilog Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/ebmc_util.h>
#include <util/mathematical_types.h>
#include <util/std_types.h>

#include "verilog_expr.h"
#include "verilog_typecheck.h"
#include "verilog_typecheck_expr.h"
#include "verilog_types.h"

#include <set>

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

Function: verilog_typecheckt::instantiate_interface_ports

  Inputs:

 Outputs:

 Purpose: For each port that has an interface type, instantiate
          the interface under the port's identifier so that
          hierarchical member access (e.g., bus.i) works.

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

    // Check if this port has an interface type
    if(port_symbol->type.id() != ID_verilog_module_instance)
      continue;

    irep_idt interface_base_name = port_symbol->type.get(ID_base_name);
    if(interface_base_name.empty())
      continue;

    // Find the interface source and instantiate it under this port
    irep_idt interface_module_id = verilog_module_symbol(interface_base_name);

    exprt::operandst no_parameters;
    std::map<irep_idt, exprt> no_defparams;

    instantiate_module(
      port_symbol->location,
      interface_module_id,
      interface_base_name,
      port_identifier,
      no_parameters,
      no_defparams);

    // Update the instance symbol value to record the module binding
    symbolt &port_sym = symbol_table_lookup(port_identifier);
    port_sym.value =
      verilog_module_instancet{id2string(port_identifier) + "$module"};

    // Handle modport port expressions (IEEE 1800-2017 25.5.2)
    irep_idt modport_name = port_symbol->type.get(ID_verilog_modport);
    if(!modport_name.empty())
    {
      instantiate_modport_port_expressions(
        port_identifier, interface_module_id, modport_name);
    }
  }
}

/*******************************************************************\

Function: verilog_typecheckt::instantiate_modport_port_expressions

  Inputs:

 Outputs:

 Purpose: For modport port expressions (IEEE 1800-2017 25.5.2),
          create wire symbols that alias the named ports to
          their underlying expressions. The expression is stored
          in the symbol's value; the type is resolved by
          type-checking the expression in the interface context.

\*******************************************************************/

void verilog_typecheckt::instantiate_modport_port_expressions(
  const irep_idt &port_identifier,
  const irep_idt &interface_module_id,
  const irep_idt &modport_name)
{
  // Find the interface source
  auto source_it =
    symbol_table.symbols.find(id2string(interface_module_id) + "$source");

  if(source_it == symbol_table.symbols.end())
    return;

  const auto &interface_source =
    to_verilog_module_source(source_it->second.type.find(ID_module_source));

  // The instantiated module identifier for the interface under this port
  irep_idt instantiated_module_id = id2string(port_identifier) + "$module";

  // Search through module items for the modport declaration
  for(auto &item : interface_source.module_items())
  {
    if(item.id() != ID_verilog_modport_declaration)
      continue;

    // Each operand is a modport_item
    for(auto &modport_item : item.operands())
    {
      if(modport_item.get(ID_base_name) != modport_name)
        continue;

      // Found the matching modport item. Process its port declarations.
      for(auto &port_decl : modport_item.operands())
      {
        // Each port_decl is a direction node (ID_input, ID_output, etc.)
        // with identifiers as operands.
        for(auto &port_id : port_decl.operands())
        {
          // Check if this is a port expression (has ID_value)
          const auto &value_irep = port_id.find(ID_value);
          if(value_irep.is_nil())
            continue;

          // This is a modport port expression:
          //   .port_name(expression)
          irep_idt port_expr_name = port_id.get(ID_base_name);
          if(port_expr_name.empty())
            continue;

          irep_idt full_identifier =
            id2string(port_identifier) + "." + id2string(port_expr_name);

          // Skip if the symbol already exists
          if(
            symbol_table.symbols.find(full_identifier) !=
            symbol_table.symbols.end())
            continue;

          // Type-check the expression in the interface instance context
          // to determine its type.
          exprt value_expr = static_cast<const exprt &>(value_irep);

          verilog_typecheck_exprt expr_checker(
            standard,
            warn_implicit_nets,
            ns,
            instantiated_module_id,
            port_identifier,
            get_message_handler());

          expr_checker.convert_expr(value_expr);

          // Create a wire symbol for the port expression
          symbolt symbol{full_identifier, value_expr.type(), ID_Verilog};

          symbol.base_name = port_expr_name;
          symbol.module = module_identifier;
          symbol.pretty_name = strip_verilog_root_prefix(full_identifier);
          symbol.is_state_var = true;
          symbol.is_lvalue = true;
          symbol.value = value_expr;

          if(port_decl.id() == ID_input)
            symbol.is_input = true;
          else if(port_decl.id() == ID_output)
            symbol.is_output = true;
          else if(port_decl.id() == ID_inout)
          {
            symbol.is_input = true;
            symbol.is_output = true;
          }

          symbol_table.add(symbol);
        }
      }
    }
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
  else if(module_item.id() == ID_verilog_generate_decl)
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
