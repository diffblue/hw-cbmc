/*******************************************************************\

Module: Verilog Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>

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

void verilog_typecheckt::module_interface()
{
  // get port classes and types
  
  module_identifier=module_symbol.name;

  const irept &module_source=module_symbol.type.find(ID_module_source);
  const irept &module_items=module_source.find(ID_module_items);

  // first do module items
  forall_irep(it, module_items.get_sub())
    interface_module_item(
      static_cast<const verilog_module_itemt &>(*it));

  // now check port names
  interface_ports(module_symbol.type.add(ID_ports).get_sub());
}

/*******************************************************************\

Function: verilog_typecheckt::interface_ports

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::interface_ports(irept::subt &ports)
{
  const irept &module_source=module_symbol.type.find(ID_module_source);
  const irept &module_ports=module_source.find(ID_ports);

  ports.resize(module_ports.get_sub().size());
  std::map<irep_idt, unsigned> port_names;

  unsigned nr=0;

  forall_irep(it, module_ports.get_sub())
  {
    assert(it->id()==ID_decl);
    
    const verilog_declt &decl=to_verilog_decl(*it);

    assert(decl.operands().size()==1);
    assert(decl.op0().id()==ID_symbol);
    
    const irep_idt &name=decl.op0().get(ID_identifier);
    const irep_idt &port_class=decl.get(ID_class);
    
    if(name.empty())
    {
      error().source_location=static_cast<const exprt &>(*it).source_location();
      error() << "empty port name (module "
              << module_symbol.base_name << ')' << eom;
      throw 0;
    }

    if(port_names.find(name)!=
       port_names.end())
    {
      err_location(decl.op0());
      error() << "duplicate port name: `" << name << '\'' << eom;
      throw 0;
    }

    irep_idt identifier=
      id2string(module_identifier)+"."+id2string(name);
      
    const symbolt *port_symbol=0;
    
    if(port_class.empty())
    {
      // find the symbol
      
      if(ns.lookup(identifier, port_symbol))
      {
        err_location(decl.op0());
        error() << "port `" << name << "' not declared" << eom;
        throw 0;
      }
    }
    else
    {
      // add the symbol
      symbolt new_symbol;
    
      new_symbol.name=identifier;

      if(port_class==ID_input)
      {
        new_symbol.is_input=true;
      }
      else if(port_class==ID_output)
      {
        new_symbol.is_output=true;
      }
      else if(port_class==ID_output_register)
      {
        new_symbol.is_output=true;
        new_symbol.is_state_var=true;
      }
      else if(port_class==ID_inout)
      {
        new_symbol.is_input=true;
        new_symbol.is_output=true;
      }

      new_symbol.mode=mode;
      new_symbol.module=module_identifier;
      new_symbol.value.make_nil();
      convert_type(decl.type(), new_symbol.type);
      new_symbol.base_name=name;
      new_symbol.pretty_name=strip_verilog_prefix(new_symbol.name);
      
      symbolt *s;

      if(symbol_table.move(new_symbol, s))
      {
        warning().source_location=decl.op0().source_location();
        warning() << "port `" << name << "' is also declared" << eom;
      }
      
      port_symbol=s;
    }

    if(!port_symbol->is_input && !port_symbol->is_output)
    {
      err_location(decl.op0());
      error() << "port `" << name 
              << "' not declared as input or output" << eom;
      throw 0;
    }

    ports[nr].set("#name", name);
    ports[nr].id(ID_symbol);
    ports[nr].set(ID_identifier, identifier);
    ports[nr].set(ID_C_source_location, decl.op0().source_location());
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
      convert_type(decl.type(), return_type);
    else
      return_type=empty_typet();
    
    symbol.type=code_typet();
    symbol.type.add(ID_return_type)=return_type;

    symbol.base_name=decl.get_identifier();
    symbol.name=
      id2string(symbol.module)+"."+
      id2string(symbol.base_name);
    symbol.pretty_name=strip_verilog_prefix(symbol.name);

    if(symbol_table.move(symbol, new_symbol))
    {
      err_location(decl);
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

  const irept::subt &declarations=decl.declarations();
  
  forall_irep(it, declarations)
    interface_module_item(to_verilog_module_item(*it));
      
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
  
  if(port_class==ID_function ||
     port_class==ID_task ||
     port_class==ID_genvar)
  {
    err_location(decl);
    error() << "this kind of declaration is not expected here" << eom;
    throw 0;
  }
  else if(port_class==ID_integer)
  {
    // we treat these as unbounded integers
    type=integer_typet();
    symbol.is_lvalue=true;
  }
  else if(port_class==ID_realtime)
  {
    symbol.is_lvalue=true;
    type=verilog_realtime_typet();
  }
  else
  {
    convert_type(decl.type(), type);
    
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
    else if(port_class==ID_reg)
    {
    }
    else if(port_class==ID_wire)
    {
      err_location(decl);
      error() << "wires are not allowed here" << eom;
      throw 0;
    }
    else
    {
      err_location(decl);
      error() << "unexpected port class: `" << port_class << '\'' << eom;
      throw 0;
    }    
  }
  
  forall_operands(it2, decl)
  {
    if(it2->id()==ID_symbol)
    {
      symbol.base_name=it2->get(ID_identifier);
      symbol.type=type;
    }
    else if(it2->id()==ID_equal)
    {
      if(it2->operands().size()!=2)
      {
        error() << "expected two operands in assignment" << eom;
        throw 0;
      }

      if(it2->op0().id()!=ID_symbol)
      {
        error() << "expected symbol on left hand side of assignment"
                   " but got `" << to_string(it2->op0()) << '\'' << eom;
        throw 0;
      }

      symbol.base_name=it2->op0().get(ID_identifier);
      symbol.type=type;
    }
    else if(it2->id()==ID_array)
    {
      symbol.base_name=it2->get(ID_identifier);
      symbol.type=array_type(*it2, type);
    }
    else
    {
      err_location(*it2);
      error() << "unexpected declaration: " << it2->id() << eom;
      throw 0;
    }

    if(symbol.base_name=="")
    {
      err_location(decl);
      error() << "empty symbol name" << eom;
      throw 0;
    }

    symbol.name=
      id2string(function_or_task_name)+"."+
      id2string(symbol.base_name);

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
      parameters.push_back(code_typet::parametert());
      code_typet::parametert &parameter=parameters.back();
      parameter.set_base_name(symbol.base_name);
      parameter.set_identifier(symbol.name);
      parameter.type()=symbol.type;
      parameter.set(ID_output, output);
      parameter.set(ID_input, input);
    }

    symbol_tablet::symbolst::const_iterator result=
      symbol_table.symbols.find(symbol.name);
      
    if(result!=symbol_table.symbols.end())
    {
      err_location(decl);
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
  else if(port_class==ID_integer)
  {
    // we treat these as unbounded integers
    type=integer_typet();
    symbol.is_lvalue=true;
  }
  else if(port_class==ID_genvar)
  {
    type=genvar_typet();
  }
  else if(port_class==ID_realtime)
  {
    symbol.is_lvalue=true;
    type=verilog_realtime_typet();
  }
  else
  {
    convert_type(decl.type(), type);

    if(port_class==ID_input)
      symbol.is_input=true;
    else if(port_class==ID_output)
      symbol.is_output=true;
    else if(port_class==ID_output_register)
    {
      symbol.is_output=true;
      symbol.is_state_var=true;
    }
    else if(port_class==ID_inout)
    {
      symbol.is_input=true;
      symbol.is_output=true;
    }
    else if(port_class==ID_reg)
      symbol.is_state_var=true;
    else if(port_class==ID_wire)
    {
    }
    else
    {
      error() << "unexpected port class: `" << port_class
              << '\'' << eom;
      throw 0;
    }
  }
  
  forall_operands(it2, decl)
  {
    if(it2->id()==ID_symbol)
    {
      symbol.base_name=it2->get(ID_identifier);
      symbol.location=it2->source_location();  
      
      if(it2->type().is_nil())
        symbol.type=type;
      else if(it2->type().id()==ID_array)
        symbol.type=array_type(it2->type(), type);
      else
      {
        error() << "unexpected type on declarator" << eom;
        throw 0;
      }
    }
    else if(it2->id()==ID_equal)
    {
      if(it2->operands().size()!=2)
      {
        error() << "expected two operands in assignment" << eom;
        throw 0;
      }

      if(it2->op0().id()!=ID_symbol)
      {
        error() << "expected symbol on left hand side of assignment"
                   " but got `" << to_string(it2->op0()) << '\'' << eom;
        throw 0;
      }

      symbol.base_name=it2->op0().get(ID_identifier);
      symbol.location=it2->op0().source_location();  
      symbol.type=type;
    }
    else
    {
      err_location(*it2);
      error() << "unexpected declaration: " << it2->id() << eom;
      throw 0;
    }

    if(symbol.base_name.empty())
    {
      err_location(decl);
      error() << "empty symbol name" << eom;
      throw 0;
    }

    symbol.name=
      id2string(symbol.module)+"."+
      (named_blocks.empty()?"":named_blocks.back())+
      id2string(symbol.base_name);

    symbol.pretty_name=
      strip_verilog_prefix(symbol.name);

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
        err_location(decl);
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
        err_location(decl);
        error() << "symbol `" << symbol.base_name
                << "' is declared both as input and as register" << eom;
        throw 0;
      }
    }
  }
}

/*******************************************************************\

Function: verilog_typecheckt::interface_parameter

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::interface_parameter(const exprt &expr)
{
  symbolt symbol;

  symbol.mode=mode;
  symbol.module=module_identifier;
  symbol.base_name=expr.get(ID_identifier);

  symbol.name=id2string(symbol.module)+"."+
              id2string(symbol.base_name);

  symbol.pretty_name=strip_verilog_prefix(symbol.name);

  symbol.is_macro=true;
  symbol.value=static_cast<const exprt &>(expr.find(ID_value));

  if(symbol.base_name.empty())
  {
    err_location(expr);
    error() << "empty symbol name" << eom;
    throw 0;
  }

  convert_expr(symbol.value);
  symbol.type=symbol.value.type();

  symbolt *new_symbol;

  if(symbol_table.move(symbol, new_symbol))
  {
    err_location(expr);
    error() << "conflicting definition of symbol `"
            << symbol.base_name << '\'' << eom;
    throw 0;
  }  
}

/*******************************************************************\

Function: verilog_typecheckt::interface_parameter_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::interface_parameter_decl(
  const exprt &statement)
{
  forall_operands(it, statement)
    interface_parameter(*it);
}

/*******************************************************************\

Function: verilog_typecheckt::convert_inst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::interface_inst(
  const verilog_module_itemt &statement)
{
  forall_operands(it, statement)
    interface_inst(statement, *it);
}

/*******************************************************************\

Function: verilog_typecheckt::interface_inst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::interface_inst(
  const verilog_module_itemt &statement,
  const exprt &op)
{
  bool primitive=statement.id()==ID_inst_builtin;
  const exprt &range=static_cast<const exprt &>(op.find(ID_range));

  mp_integer msb, lsb;
  
  if(range.is_nil() || range.id().empty())
    msb=lsb=0;
  else
    convert_range(range, msb, lsb);

  irep_idt identifier=
    verilog_module_symbol(id2string(statement.get(ID_module)));

  // add symbol
  symbolt symbol;

  symbol.mode=mode;
  symbol.base_name=op.get(ID_instance);
  symbol.type=typet(primitive?ID_primitive_module_instance:ID_module_instance);
  symbol.module=module_identifier;
  symbol.name=
    id2string(symbol.module)+"."+
    id2string(symbol.base_name);
  symbol.pretty_name=strip_verilog_prefix(symbol.name);
  symbol.value.set(ID_module, identifier);

  if(symbol_table.add(symbol))
  {
    err_location(op);
    error() << "duplicate definition of identifier `" 
            << symbol.base_name << "' in module `"
            << module_symbol.base_name << '\'' << eom;
    throw 0;
  }
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
    interface_parameter_decl(module_item);
  else if(module_item.id()==ID_inst ||
          module_item.id()==ID_inst_builtin)
    interface_inst(module_item);
  else if(module_item.id()==ID_always)
    interface_statement(to_verilog_always(module_item).statement());
  else if(module_item.id()==ID_initial)
    interface_statement(to_verilog_initial(module_item).statement());
  else if(module_item.id()==ID_generate_block)
  {
    forall_irep(it, module_item.get_sub())
      interface_module_item(
        static_cast<const verilog_module_itemt &>(*it));
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
    interface_module_decl(to_verilog_decl(statement));
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
    irep_idt identifier=statement.get_identifier();
  
    // need to add to symbol table
    symbolt symbol;

    symbol.mode=mode;
    symbol.base_name=identifier;
    symbol.type=typet(ID_named_block);
    symbol.module=module_identifier;
    symbol.name=
      id2string(symbol.module)+"."+
      (named_blocks.empty()?"":named_blocks.back())+
      id2string(symbol.base_name);
    symbol.pretty_name=strip_verilog_prefix(symbol.name);
    symbol.value=nil_exprt();

    if(symbol_table.add(symbol))
    {
      err_location(statement);
      error() << "duplicate definition of identifier `" 
              << symbol.base_name << "' in module `"
              << module_symbol.base_name << '\'' << eom;
      throw 0;
    }    

    enter_named_block(identifier);
  }

  // do decl
  const exprt &decl=static_cast<const exprt &>(
    statement.find("decl-brace"));

  forall_operands(it, decl)
    interface_module_item(
      static_cast<const verilog_module_itemt &>(*it));
    
  // do block itself

  forall_operands(it, statement)
    interface_statement(
      static_cast<const verilog_statementt &>(*it));

  if(is_named)
    named_blocks.pop_back();
}
