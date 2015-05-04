/*******************************************************************\

Module: Verilog Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>

#include <util/std_types.h>

#include "verilog_typecheck.h"
#include "verilog_expr.h"

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

  forall_irep(it, module_items.get_sub())
    interface_module_item(
      static_cast<const verilog_module_itemt &>(*it));

  // get port names
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
    
    if(name=="")
    {
      err_location(*it);
      str << "empty port name (module "
          << module_symbol.base_name << ")";
      throw 0;
    }

    if(port_names.find(name)!=
       port_names.end())
    {
      err_location(decl.op0());
      str << "duplicate port name: `" << name << "'";
      throw 0;
    }

    irep_idt identifier=
      id2string(module_identifier)+"."+id2string(name);
      
    const symbolt *port_symbol=0;
    
    if(port_class=="")
    {
      // find the symbol
      
      if(lookup(identifier, port_symbol))
      {
        err_location(decl.op0());
        str << "port `" << name << "' not declared";
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
      
      symbolt *s;

      if(symbol_table.move(new_symbol, s))
      {
        err_location(decl.op0());
        str << "port `" << name << "' is also declared";
        warning();
      }
      
      port_symbol=s;
    }

    if(!port_symbol->is_input && !port_symbol->is_output)
    {
      err_location(decl.op0());
      str << "port `" << name << "' not declared as input or output";
      throw 0;
    }

    ports[nr].set("#name", name);
    ports[nr].id(ID_symbol);
    ports[nr].set(ID_identifier, identifier);
    ports[nr].set(ID_C_source_location, decl.op0().location());
    ports[nr].set(ID_type, port_symbol->type);
    ports[nr].set(ID_input, port_symbol->is_input);
    ports[nr].set(ID_output, port_symbol->is_output);

    port_names[name]=nr;
    
    nr++;
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
    symbol.value.make_nil();

    typet return_type;

    if(decl_class==ID_function)
      convert_type(decl.type(), return_type);
    else
      return_type=empty_typet();
    
    symbol.type=typet(ID_code);
    symbol.type.add(ID_return_type)=return_type;

    symbol.base_name=decl.get_identifier();
    symbol.name=
      id2string(symbol.module)+"."+
      id2string(symbol.base_name);

    if(symbol_table.move(symbol, new_symbol))
    {
      err_location(decl);
      str << "symbol `" << symbol.base_name
          << "' is already declared";
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

    symbol_table.move(return_symbol);
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
    str << "this kind of declaration is not expected here";
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
    type=typet("verilog_realtime");
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
      str << "wires are not allowed here";
      throw 0;
    }
    else
    {
      err_location(decl);
      str << "unexpected port class: `" << port_class << "'";
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
        throw "expected two operands in assignment";

      if(it2->op0().id()!=ID_symbol)
      {
        str << "expected symbol on left hand side of assignment"
               " but got `" << to_string(it2->op0()) << "'";
        throw 0;
      }

      symbol.base_name=it2->op0().get(ID_identifier);
      symbol.type=type;
    }
    else if(it2->id()==ID_array)
    {
      symbol.base_name=it2->get(ID_identifier);
      array_type(*it2, type, symbol.type);
    }
    else
    {
      err_location(*it2);
      throw "unexpected declaration: "+it2->id_string();
    }

    if(symbol.base_name=="")
    {
      err_location(decl);
      str << "empty symbol name";
      throw 0;
    }

    symbol.name=
      id2string(function_or_task_name)+"."+
      id2string(symbol.base_name);

    if(input || output)
    {
      symbol_tablet::symbolst::iterator s_it=
        symbol_table.symbols.find(function_or_task_name);
      assert(s_it!=symbol_table.symbols.end());
      symbolt &function_or_task_symbol=s_it->second;
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

    symbol_tablet::symbolst::iterator result=
      symbol_table.symbols.find(symbol.name);
      
    if(result!=symbol_table.symbols.end())
    {
      err_location(decl);
      str << "symbol `" << symbol.base_name
          << "' is already declared";
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
    type=typet(ID_genvar);
  }
  else if(port_class==ID_realtime)
  {
    symbol.is_lvalue=true;
    type=typet("verilog_realtime");
  }
  else
  {
    convert_type(decl.type(), type);

    if(port_class==ID_input)
      symbol.is_input=true;
    else if(port_class==ID_output)
      symbol.is_output=true;
    else if(port_class=="output-register")
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
      str << "unexpected port class: `" << port_class << "'";
      throw 0;
    }
  }
  
  forall_operands(it2, decl)
  {
    if(it2->id()==ID_symbol)
    {
      symbol.base_name=it2->get(ID_identifier);
      
      if(it2->type().is_nil())
        symbol.type=type;
      else if(it2->type().id()==ID_array)
        array_type(it2->type(), type, symbol.type);
      else
      {
        str << "unexpected type on declarator";
        throw 0;
      }
    }
    else if(it2->id()==ID_equal)
    {
      if(it2->operands().size()!=2)
        throw "expected two operands in assignment";

      if(it2->op0().id()!=ID_symbol)
      {
        str << "expected symbol on left hand side of assignment"
               " but got `" << to_string(it2->op0()) << "'";
        throw 0;
      }

      symbol.base_name=it2->op0().get(ID_identifier);
      symbol.type=type;
    }
    else
    {
      err_location(*it2);
      throw "unexpected declaration: "+it2->id_string();
    }

    if(symbol.base_name=="")
    {
      err_location(decl);
      str << "empty symbol name";
      throw 0;
    }

    symbol.name=
      id2string(symbol.module)+"."+
      id2string(symbol.base_name);

    symbol_tablet::symbolst::iterator result=
      symbol_table.symbols.find(symbol.name);
      
    if(result==symbol_table.symbols.end())
      symbol_table.add(symbol);
    else
    {
      symbolt &osymbol=result->second;
      
      if(osymbol.type.id()==ID_code)
      {
        err_location(decl);
        str << "symbol `" << symbol.base_name
            << "' is already declared";
        throw 0;
      }

      if(symbol.type!=osymbol.type)
      {
        if(get_width(symbol.type)>get_width(osymbol.type))
          osymbol.type=symbol.type;
      }

      osymbol.is_input   =symbol.is_input    || osymbol.is_input;
      osymbol.is_output  =symbol.is_output   || osymbol.is_output;
      osymbol.is_state_var=symbol.is_state_var || osymbol.is_state_var;

      // a register can't be an input as well
      if(osymbol.is_input && osymbol.is_state_var)
      {
        err_location(decl);
        str << "symbol `" << symbol.base_name
            << "' is declared both as input and as register";
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

  symbol.is_macro=true;
  symbol.value=static_cast<const exprt &>(expr.find(ID_value));

  if(symbol.base_name=="")
  {
    err_location(expr);
    str << "empty symbol name";
    throw 0;
  }

  convert_expr(symbol.value);
  symbol.type=symbol.value.type();

  symbolt *new_symbol;

  if(symbol_table.move(symbol, new_symbol))
  {
    err_location(expr);
    str << "conflicting definition of symbol `"
        << symbol.base_name << "'";
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
  const exprt &range=static_cast<const exprt &>(op.find(ID_range));

  mp_integer msb, lsb;
  
  if(range.is_nil() || range.id()=="")
    msb=lsb=0;
  else
    convert_range(range, msb, lsb);

  irep_idt identifier=
    verilog_module_symbol(id2string(statement.get(ID_module)));

  // add symbol
  symbolt symbol;

  symbol.mode=mode;
  symbol.base_name=op.get(ID_instance);
  symbol.type=typet(ID_module_instance);
  symbol.module=module_identifier;
  symbol.name=
    id2string(symbol.module)+"."+
    id2string(symbol.base_name);
  symbol.value.set(ID_module, identifier);

  if(symbol_table.add(symbol))
  {
    err_location(op);
    str << "duplicate definition of identifier `" 
        << symbol.base_name << "' in module `"
        << module_symbol.base_name << "'";
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
    if(function_or_task_name=="")
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
  else if(statement.id()==ID_event_guard)
  {
    if(statement.operands().size()!=2)
      throw "event_guard expected to have two operands";

    interface_statement(
      to_verilog_event_guard(statement).body());
  }
  else if(statement.id()==ID_delay)
  {
    if(statement.operands().size()!=2)
      throw "delay expected to have two operands";

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
  // identifier
  //const irep_idt &block_identifier=statement.get(ID_identifier);

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
}
