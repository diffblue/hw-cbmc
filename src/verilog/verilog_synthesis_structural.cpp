/*******************************************************************\

Module: Verilog Synthesis (Structural)

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_synthesis_class.h"

#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/std_expr.h>

#include "verilog_expr.h"
#include "verilog_synthesis.h"

#include <cassert>

/*******************************************************************\

Function: verilog_synthesist::instantiate_port

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::instantiate_port(
  const module_typet::portt &port,
  const exprt &value,
  const source_locationt &source_location,
  transt &trans)
{
  symbol_exprt port_symbol{port.identifier(), port.type()};

  // Much like
  //   always @(*) port = value for an input, and
  //   always @(*) value = port for an output.
  // Note that the types need not match.
  exprt lhs, rhs;

  if(port.output())
  {
    lhs = value;
    rhs = typecast_exprt::conditional_cast(port_symbol, value.type());
  }
  else
  {
    lhs = port_symbol;
    rhs = typecast_exprt::conditional_cast(value, port_symbol.type());
  }

  verilog_forcet assignment{lhs, rhs};

  assignment.add_source_location() = source_location;

  verilog_event_guardt event_guard;
  event_guard.add_source_location() = source_location;
  event_guard.body() = assignment;

  verilog_always_baset always(ID_verilog_always, event_guard, source_location);
  synth_always_base(always);
}

/*******************************************************************\

Function: verilog_synthesist::instantiate_ports

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::instantiate_ports(
  const irep_idt &instance,
  const verilog_instt::instancet &inst,
  const symbolt &symbol,
  transt &trans)
{
  if(inst.connections().empty())
    return;

  auto &module_type = to_module_type(symbol.type);

  // named port connection?

  if(inst.named_port_connections())
  {
    const auto &ports = module_type.ports();
    auto port_map = module_type.port_map();

    // no requirement that all ports are connected
    for(const auto &connection : inst.connections())
    {
      if(connection.id() == ID_verilog_wildcard_port_connection)
        throw errort{}.with_location(connection.source_location())
          << "no support for wildcard port connection";

      auto &named_connection = to_verilog_named_port_connection(connection);
      auto port_it =
        port_map.find(to_symbol_expr(named_connection.port()).get_identifier());
      CHECK_RETURN(port_it != port_map.end());
      auto &port = port_it->second;
      const exprt &value = named_connection.value();

      if(value.is_not_nil())
      {
        instantiate_port(port, value, inst.source_location(), trans);
      }
    }

    std::set<irep_idt> connected_ports;

    for(const auto &connection : inst.connections())
    {
      auto &named_connection = to_verilog_named_port_connection(connection);
      connected_ports.insert(
        to_symbol_expr(named_connection.port()).get_identifier());
    }

    // unconnected inputs may be given a default value
    for(auto &port : ports)
      if(port.input())
      {
        auto identifier = port.identifier();
        if(connected_ports.find(identifier) == connected_ports.end())
        {
          auto &port_symbol = ns.lookup(identifier);
          if(port_symbol.value.is_not_nil())
            instantiate_port(
              port, port_symbol.value, inst.source_location(), trans);
        }
      }
  }
  else // just a list without names
  {
    const auto &ports = module_type.ports();

    if(inst.connections().size() != ports.size())
    {
      throw errort().with_location(inst.source_location())
        << "wrong number of ports: expected " << ports.size() << " but got "
        << inst.connections().size();
    }

    auto p_it = ports.begin();

    for(const auto &connection : inst.connections())
    {
      // 1800-2017 23.3.3.2 says
      // "If left unconnected, the port shall have the default
      // initial value corresponding to the data type."
      // Simulators don't agree on this, and we hence leave the port
      // unconstrained.
      if(connection.is_not_nil())
      {
        instantiate_port(*p_it, connection, inst.source_location(), trans);
      }

      p_it++;
    }
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_module_instance

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_module_instance(
  const verilog_instt &statement,
  transt &trans_dest)
{
  for(auto &instance : statement.instances())
  {
    const irep_idt &module_identifier = instance.module_identifier();

    // must be in symbol_table
    const symbolt &module_symbol = ns.lookup(module_identifier);

    // get the transition relation of the instantiated module
    auto trans_inst = verilog_synthesis(
      symbol_table,
      module_identifier,
      standard,
      ignore_initial,
      initial_zero,
      get_message_handler());

    expand_module_instance(module_symbol, trans_inst, instance, trans_dest);
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_module_instance_builtin

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_module_instance_builtin(
  const verilog_inst_builtint &module_item,
  transt &trans)
{
  const irep_idt &module = module_item.module_base_name();

  for(auto &instance : module_item.instances())
  {
    // check built-in ones
    if(
      module == ID_bufif0 || module == ID_bufif1 || module == ID_notif0 ||
      module == ID_notif1)
    {
      // add to general constraints

      exprt constraint = instance;
      constraint.id("verilog-primitive-module");
      constraint.type() = bool_typet();
      constraint.set(ID_module, module);

      assert(trans.operands().size() == 3);
      trans.invar().add_to_operands(std::move(constraint));
    }
    else if(
      module == ID_nmos || module == ID_pmos || module == ID_rnmos ||
      module == ID_rpmos)
    {
      // add to general constraints

      exprt constraint = instance;
      constraint.id("verilog-primitive-module");
      constraint.type() = bool_typet();
      constraint.set(ID_module, module);

      assert(trans.operands().size() == 3);
      trans.invar().add_to_operands(std::move(constraint));
    }
    else if(
      module == ID_and || module == ID_nand || module == ID_or ||
      module == ID_nor || module == ID_xor || module == ID_xnor)
    {
      // 1800-2017 28.4 and, nand, nor, or, xor, and xnor gates
      DATA_INVARIANT(
        instance.connections().size() >= 2,
        "binary primitive gates should have at least two connections");

      // One output, one or more inputs.
      auto &connections = instance.connections();
      auto &output = connections[0];

      irep_idt id = instance.type().id() == ID_bool
                      ? module
                      : irep_idt{"bit" + id2string(module)};

      exprt::operandst operands;

      // iterate over the module inputs
      for(std::size_t i = 1; i < connections.size(); i++)
      {
        operands.push_back(connections[i]);
      }

      auto op = exprt{id, instance.type(), std::move(operands)};

      equal_exprt constraint{output, op};
      trans.invar().add_to_operands(std::move(constraint));
    }
    else if(module == ID_buf)
    {
      assert(instance.connections().size() >= 2);

      for(unsigned i = 0; i < instance.connections().size() - 1; i++)
      {
        equal_exprt constraint{
          instance.connections()[i], instance.connections().back()};

        assert(trans.operands().size() == 3);
        trans.invar().add_to_operands(std::move(constraint));
      }
    }
    else if(module == ID_not)
    {
      assert(instance.connections().size() >= 2);

      // May have multiple outputs. The input is the last connection.
      auto &input = instance.connections().back();
      exprt rhs;

      if(input.type().id() == ID_bool)
        rhs = not_exprt{input};
      else
        rhs = bitnot_exprt{input};

      rhs.add_source_location() = module_item.source_location();

      for(std::size_t i = 0; i < instance.connections().size() - 1; i++)
      {
        auto &lhs = instance.connections()[i];
        auto constraint = equal_exprt{lhs, rhs};
        trans.invar().add_to_operands(std::move(constraint));
      }
    }
    else if(
      module == "tranif0" || module == "tranif1" || module == "rtranif1" ||
      module == "rtranif0")
    {
      // add to general constraints

      exprt constraint = instance;
      constraint.id("verilog-primitive-module");
      constraint.type() = bool_typet();
      constraint.set(ID_module, module);

      assert(trans.operands().size() == 3);
      trans.invar().add_to_operands(std::move(constraint));
    }
    else if(module == "tran" || module == "rtran")
    {
      // add to general constraints

      exprt constraint = instance;
      constraint.id("verilog-primitive-module");
      constraint.type() = bool_typet();
      constraint.set(ID_module, module);

      assert(trans.operands().size() == 3);
      trans.invar().add_to_operands(std::move(constraint));
    }
    else
    {
      throw errort().with_location(module_item.source_location())
        << "do not know how to synthesize " << module;
    }
  }
}

/*******************************************************************\

Function: verilog_synthesist::find_module_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::vector<irep_idt>
verilog_synthesist::find_module_symbols(const symbolt &module_symbol) const
{
  std::vector<irep_idt> result;

  auto lower = symbol_table.symbol_module_map.lower_bound(module_symbol.module);
  auto upper = symbol_table.symbol_module_map.upper_bound(module_symbol.module);

  for(auto it = lower; it != upper; it++)
  {
    result.push_back(it->second);
  }

  return result;
}

/*******************************************************************\

Function: verilog_synthesist::expand_module_instance

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::expand_module_instance(
  const symbolt &module_symbol,
  const transt &trans_inst,
  const verilog_instt::instancet &instance,
  transt &trans_dest)
{
  construct = constructt::OTHER;

  // do the trans of the instantiated module
  for(std::size_t i = 0; i < 3; i++)
    trans_dest.operands()[i].add_to_operands(trans_inst.operands()[i]);

  instantiate_ports(instance.base_name(), instance, module_symbol, trans_dest);
}
