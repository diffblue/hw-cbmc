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

    const irep_idt &name = declarator.identifier();

    if(name.empty())
    {
      throw errort().with_location(decl.source_location())
        << "empty port name (module " << module_symbol.base_name << ')';
    }

    if(port_names.find(name)!=
       port_names.end())
    {
      error().source_location = declarator.source_location();
      error() << "duplicate port name: `" << name << '\'' << eom;
      throw 0;
    }

    irep_idt identifier=
      id2string(module_identifier)+"."+id2string(name);
      
    const symbolt *port_symbol=0;

    // find the symbol

    if(ns.lookup(identifier, port_symbol))
    {
      throw errort().with_location(declarator.source_location())
        << "port `" << name << "' not declared";
    }

    if(!port_symbol->is_input && !port_symbol->is_output)
    {
      error().source_location = declarator.source_location();
      error() << "port `" << name 
              << "' not declared as input or output" << eom;
      throw 0;
    }

    ports[nr].set("#name", name);
    ports[nr].id(ID_symbol);
    ports[nr].set(ID_identifier, identifier);
    ports[nr].set(ID_C_source_location, declarator.source_location());
    ports[nr].set(ID_type, port_symbol->type);
    ports[nr].set(ID_input, port_symbol->is_input);
    ports[nr].set(ID_output, port_symbol->is_output);

    port_names[name]=nr;
    
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

Function: verilog_typecheckt::interface_function_or_task

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::interface_function_or_task(
  const verilog_declt &decl)
{
  irep_idt decl_class=decl.get_class();

  // only add symbol for now
  symbolt *new_symbol;
  
  {
    symbolt symbol;

    symbol.mode=mode;
    symbol.module=module_identifier;
    symbol.value=decl;

    typet return_type;

    if(decl_class==ID_function)
      return_type = convert_type(decl.type());
    else
      return_type=empty_typet();

    symbol.type = code_typet{{}, return_type};

    symbol.base_name=decl.get_identifier();
    symbol.name = hierarchical_identifier(symbol.base_name);
    symbol.pretty_name=strip_verilog_prefix(symbol.name);

    if(symbol_table.move(symbol, new_symbol))
    {
      error().source_location = decl.source_location();
      error() << "symbol `" << symbol.base_name
              << "' is already declared" << eom;
      throw 0;
    }
  }

  function_or_task_name=new_symbol->name;

  // add a symbol for the return value of functions

  if(decl_class==ID_function)
  {
    symbolt return_symbol;
    return_symbol.is_state_var=true;
    return_symbol.is_lvalue=true;
    return_symbol.mode=new_symbol->mode;
    return_symbol.module=new_symbol->module;
    return_symbol.base_name=new_symbol->base_name;
    return_symbol.value.make_nil();
    return_symbol.type=to_code_type(new_symbol->type).return_type();

    return_symbol.name=
      id2string(new_symbol->name)+"."+
      id2string(new_symbol->base_name);

    return_symbol.pretty_name=strip_verilog_prefix(return_symbol.name);

    symbol_table.add(return_symbol);
  }

  // do the declarations within the task/function
  auto &declarations = decl.declarations();

  for(auto &decl : declarations)
    interface_function_or_task_decl(decl);

  interface_statement(decl.body());
    
  function_or_task_name="";  
}

/*******************************************************************\

Function: verilog_typecheckt::interface_function_or_task_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::interface_function_or_task_decl(const verilog_declt &decl)
{
  symbolt symbol;
  typet type;
  bool input=false, output=false;

  symbol.mode=mode;
  symbol.module=module_identifier;
  symbol.value.make_nil();
  
  const irep_idt &port_class=decl.get_class();

  if(
    port_class == ID_function || port_class == ID_task ||
    port_class == ID_verilog_genvar)
  {
    error().source_location = decl.source_location();
    error() << "this kind of declaration is not expected here" << eom;
    throw 0;
  }
  else
  {
    type = convert_type(decl.type());

    symbol.is_state_var=true;

    if(port_class==ID_input)
    {
      input=true;
    }
    else if(port_class==ID_output)
    {
      output=true;
    }
    else if(port_class==ID_output_register)
    {
      output=true;
    }
    else if(port_class==ID_inout)
    {
      input=true;
      output=true;
    }
    else if(port_class == ID_reg || port_class == ID_var)
    {
    }
    else if(port_class==ID_wire)
    {
      error().source_location = decl.source_location();
      error() << "wires are not allowed here" << eom;
      throw 0;
    }
    else if(port_class == ID_typedef)
    {
      symbol.is_type = true;
    }
    else
    {
      if(
        type.id() == ID_integer || type.id() == ID_verilog_realtime ||
        type.id() == ID_verilog_shortreal || type.id() == ID_verilog_real)
      {
        symbol.is_lvalue = true;
      }
      else
      {
        error().source_location = decl.source_location();
        error() << "unexpected port class: `" << port_class << '\'' << eom;
        throw 0;
      }
    }    
  }

  for(auto &declarator : decl.declarators())
  {
    DATA_INVARIANT(declarator.id() == ID_declarator, "must have declarator");

    symbol.base_name = declarator.base_name();

    if(symbol.base_name.empty())
    {
      throw errort().with_location(decl.source_location())
        << "empty symbol name";
    }

    symbol.type = type;

    symbol.name = hierarchical_identifier(symbol.base_name);

    symbol.pretty_name=strip_verilog_prefix(symbol.name);

    if(input || output)
    {
      // Terminology clash: these aren't called 'parameters'
      // in Verilog terminology, but inputs and outputs.
      // We'll use the C terminology, and call them parameters.
      // Not to be confused with module parameters.
      auto s_it=symbol_table.get_writeable(function_or_task_name);
      CHECK_RETURN(s_it!=nullptr);
      symbolt &function_or_task_symbol=*s_it;
      code_typet::parameterst &parameters=
        to_code_type(function_or_task_symbol.type).parameters();
      parameters.push_back(code_typet::parametert(symbol.type));
      code_typet::parametert &parameter=parameters.back();
      parameter.set_base_name(symbol.base_name);
      parameter.set_identifier(symbol.name);
      parameter.set(ID_output, output);
      parameter.set(ID_input, input);
    }

    symbol_tablet::symbolst::const_iterator result=
      symbol_table.symbols.find(symbol.name);
      
    if(result!=symbol_table.symbols.end())
    {
      error().source_location = decl.source_location();
      error() << "symbol `" << symbol.base_name
              << "' is already declared" << eom;
      throw 0;
    }

    symbol_table.add(symbol);
  }
}

/*******************************************************************\

Function: verilog_typecheckt::interface_module_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::interface_module_decl(
  const verilog_declt &decl)
{
  assert(function_or_task_name=="");
  
  symbolt symbol;
  typet type;

  symbol.mode=mode;
  symbol.module=module_identifier;
  symbol.value.make_nil();
  const irep_idt &port_class=decl.get_class();
  
  if(port_class==ID_function ||
     port_class==ID_task)
  {
    interface_function_or_task(decl);
    return;
  }
  else if(
    port_class == ID_input || port_class == ID_output ||
    port_class == ID_output_register || port_class == ID_inout ||
    port_class == ID_verilog_genvar)
  {
    // symbol already created during elaboration
    return;
  }
  else
  {
    type=convert_type(decl.type());

    if(port_class == ID_reg || port_class == ID_var)
      symbol.is_state_var=true;
    else if(port_class==ID_wire)
    {
    }
    else if(port_class == ID_supply0)
    {
    }
    else if(port_class == ID_supply1)
    {
    }
    else if(port_class == ID_typedef)
    {
      symbol.is_type = true;
    }
    else
    {
      if(
        type.id() == ID_integer || type.id() == ID_verilog_realtime ||
        type.id() == ID_verilog_shortreal || type.id() == ID_verilog_real)
      {
        symbol.is_lvalue = true;
      }
      else
      {
        error().source_location = decl.source_location();
        error() << "unexpected port class: `" << port_class << '\'' << eom;
        throw 0;
      }
    }
  }

  for(auto &declarator : decl.declarators())
  {
    DATA_INVARIANT(declarator.id() == ID_declarator, "must have declarator");

    symbol.base_name = declarator.base_name();
    symbol.location = declarator.source_location();

    if(declarator.type().is_nil())
      symbol.type=type;
    else if(declarator.type().id() == ID_array)
      symbol.type = array_type(declarator.type(), type);
    else
    {
      error().source_location = symbol.location;
      error() << "unexpected type on declarator" << eom;
      throw 0;
    }

    if(symbol.base_name.empty())
    {
      error().source_location = decl.source_location();
      error() << "empty symbol name" << eom;
      throw 0;
    }

    symbol.name = hierarchical_identifier(symbol.base_name);
    symbol.pretty_name = strip_verilog_prefix(symbol.name);

    auto result=symbol_table.get_writeable(symbol.name);
      
    if(result==nullptr)
    {
      symbol_table.add(symbol);
    }
    else
    {
      symbolt &osymbol=*result;
      
      if(osymbol.type.id()==ID_code)
      {
        error().source_location = decl.source_location();
        error() << "symbol `" << symbol.base_name
                << "' is already declared" << eom;
        throw 0;
      }

      if(symbol.type!=osymbol.type)
      {
        if(get_width(symbol.type)>get_width(osymbol.type))
          osymbol.type=symbol.type;
      }

      osymbol.is_input    =symbol.is_input     || osymbol.is_input;
      osymbol.is_output   =symbol.is_output    || osymbol.is_output;
      osymbol.is_state_var=symbol.is_state_var || osymbol.is_state_var;

      // a register can't be an input as well
      if(osymbol.is_input && osymbol.is_state_var)
      {
        error().source_location = decl.source_location();
        error() << "symbol `" << symbol.base_name
                << "' is declared both as input and as register" << eom;
        throw 0;
      }
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
    if(function_or_task_name.empty())
      interface_module_decl(to_verilog_decl(module_item));
    else
      interface_function_or_task_decl(to_verilog_decl(module_item));
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
    if(function_or_task_name.empty())
      interface_module_decl(to_verilog_decl(statement));
    else
      interface_function_or_task_decl(to_verilog_decl(statement));
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
