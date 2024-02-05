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

void verilog_typecheckt::module_interface(
  const verilog_module_sourcet &module_source)
{
  // Check the typing of the ports
  check_module_ports(module_source.ports());
}

/*******************************************************************\

Function: verilog_typecheckt::check_module_ports

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::check_module_ports(
  const verilog_module_sourcet::port_listt &module_ports)
{
  auto &ports = module_symbol.type.add(ID_ports).get_sub();
  ports.resize(module_ports.size());
  std::map<irep_idt, unsigned> port_names;

  unsigned nr=0;

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
        << "empty port name (module " << module_symbol.base_name << ')';
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

    if(!port_symbol->is_input && !port_symbol->is_output)
    {
      throw errort().with_location(declarator.source_location())
        << "port `" << base_name << "' not declared as input or output";
    }

    ports[nr].set("#name", base_name);
    ports[nr].id(ID_symbol);
    ports[nr].set(ID_identifier, identifier);
    ports[nr].set(ID_C_source_location, declarator.source_location());
    ports[nr].set(ID_type, port_symbol->type);
    ports[nr].set(ID_input, port_symbol->is_input);
    ports[nr].set(ID_output, port_symbol->is_output);

    port_names[base_name] = nr;

    nr++;
  }

  // check that all declared ports are also in the port list
  
  for(auto it=symbol_table.symbol_module_map.lower_bound(module_identifier);
           it!=symbol_table.symbol_module_map.upper_bound(module_identifier);
           it++)
  {
    const symbolt &symbol=ns.lookup(it->second);
    
    if(symbol.is_input || symbol.is_output)
      if(port_names.find(symbol.base_name)==port_names.end())
      {
        error().source_location=symbol.location;
        error() << "port `" << symbol.base_name
                << "' not in port list" << eom;
        throw 0;
      }
  }
}

/*******************************************************************\

Function: verilog_typecheckt::convert_inst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::interface_inst(
  const verilog_inst_baset &inst_module_item)
{
  for(auto &instance : inst_module_item.instances())
    interface_inst(inst_module_item, instance);
}

/*******************************************************************\

Function: verilog_typecheckt::interface_inst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::interface_inst(
  const verilog_inst_baset &statement,
  const verilog_instt::instancet &op)
{
  bool primitive=statement.id()==ID_inst_builtin;
  const exprt &range=static_cast<const exprt &>(op.find(ID_range));

  mp_integer msb, lsb;
  
  if(range.is_nil() || range.id().empty())
    msb=lsb=0;
  else
    convert_range(range, msb, lsb);

  irep_idt instantiated_module_identifier =
    verilog_module_symbol(id2string(statement.get(ID_module)));

  // add symbol for the module instance
  symbolt symbol;

  symbol.mode=mode;
  symbol.base_name = op.base_name();
  symbol.type=typet(primitive?ID_primitive_module_instance:ID_module_instance);
  symbol.module=module_identifier;
  symbol.name = hierarchical_identifier(symbol.base_name);
  symbol.pretty_name=strip_verilog_prefix(symbol.name);
  symbol.value.set(ID_module, instantiated_module_identifier);

  if(symbol_table.add(symbol))
  {
    error().source_location = op.source_location();
    error() << "duplicate definition of identifier `" 
            << symbol.base_name << "' in module `"
            << module_symbol.base_name << '\'' << eom;
    throw 0;
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
  else if(module_item.id()==ID_parameter_decl ||
          module_item.id()==ID_local_parameter_decl)
  {
    // already done by elaborate_parameters
  }
  else if(module_item.id() == ID_inst)
    interface_inst(to_verilog_inst(module_item));
  else if(module_item.id() == ID_inst_builtin)
    interface_inst(to_verilog_inst_builtin(module_item));
  else if(module_item.id()==ID_always)
    interface_statement(to_verilog_always(module_item).statement());
  else if(module_item.id()==ID_initial)
    interface_statement(to_verilog_initial(module_item).statement());
  else if(module_item.id()==ID_generate_block)
    interface_generate_block(to_verilog_generate_block(module_item));
  else if(module_item.id() == ID_set_genvars)
    interface_module_item(to_verilog_set_genvars(module_item).module_item());
  else if(module_item.id() == ID_assert || module_item.id() == ID_assume)
  {
    // done later
  }
  else if(
    module_item.id() == ID_continuous_assign ||
    module_item.id() == ID_parameter_override)
  {
    // does not yield symbol
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
  else if(statement.id()==ID_case ||
          statement.id()==ID_casex ||
          statement.id()==ID_casez)
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
      error() << "event_guard expected to have two operands" << eom;
      throw 0;
    }

    interface_statement(
      to_verilog_event_guard(statement).body());
  }
  else if(statement.id()==ID_delay)
  {
    if(statement.operands().size()!=2)
    {
      error() << "delay expected to have two operands" << eom;
      throw 0;
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
  bool is_named=statement.is_named();
  
  if(is_named)
  {
    const irep_idt base_name = statement.base_name();

    // need to add to symbol table
    symbolt symbol;

    symbol.mode=mode;
    symbol.base_name = base_name;
    symbol.type=typet(ID_named_block);
    symbol.module=module_identifier;
    symbol.name = hierarchical_identifier(symbol.base_name);
    symbol.pretty_name=strip_verilog_prefix(symbol.name);
    symbol.value=nil_exprt();

    if(symbol_table.add(symbol))
    {
      error().source_location = statement.source_location();
      error() << "duplicate definition of identifier `" 
              << symbol.base_name << "' in module `"
              << module_symbol.base_name << '\'' << eom;
      throw 0;
    }

    enter_named_block(base_name);
  }

  // do decl
  const exprt &decl=static_cast<const exprt &>(
    statement.find("decl-brace"));

  forall_operands(it, decl)
    interface_module_item(
      static_cast<const verilog_module_itemt &>(*it));
    
  // do block itself

  for(auto &block_statement : statement.statements())
    interface_statement(block_statement);

  if(is_named)
    named_blocks.pop_back();
}
