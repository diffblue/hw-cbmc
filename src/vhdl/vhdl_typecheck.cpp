/*******************************************************************\

Module: VHDL Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>

#include <util/std_code.h>
#include <util/std_expr.h>

#include "vhdl_typecheck.h"
#include "vhdl_typecheck_class.h"

/*******************************************************************\

Function: vhdl_typecheckt::to_lower

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

dstring vhdl_typecheckt::to_lower(const dstring &src)
{
  std::string data=id2string(src);
  std::transform(data.begin(), data.end(), data.begin(), ::tolower);
  return data;
}


/*******************************************************************\

Function: vhdl_typecheckt::typecheck_architecture_entity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_typecheckt::typecheck_architecture_entity(irept &entity)
{
}

/*******************************************************************\

Function: vhdl_typecheckt::typecheck_architecture_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_typecheckt::typecheck_architecture_decl(irept &decl)
{
  for(auto & d : decl.get_sub())
  {
    if(d.id()==ID_enumeration)
    {
    }
    else if(d.id()==ID_signal)
    {
      typet &type=static_cast<typet &>(d.add(ID_type));
      typecheck_type(type);
    
      for(auto & s : d.get_sub())
      {
        symbolt new_symbol;
      
        new_symbol.base_name=s.get(ID_identifier);
        new_symbol.name=
          id2string(module_symbol->name)+"."+
          id2string(new_symbol.base_name);
        new_symbol.type=type;
        new_symbol.mode=module_symbol->mode;
      
        symbol_table.move(new_symbol);
      }
    }
    else if(d.id()==ID_component)
    {
    }
    else if(d.id()==ID_constant)
    {
    }
    else
    {
      error() << "unexpected declaration in architecture: "
              << d.id() << eom;
      throw 0;
    }
  }
}

/*******************************************************************\

Function: vhdl_typecheckt::typecheck_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_typecheckt::typecheck_expr(exprt &expr)
{
  if(expr.id()==ID_and || expr.id()==ID_nand ||
     expr.id()==ID_or  || expr.id()==ID_nor ||
     expr.id()==ID_xor || expr.id()==ID_xnor)
  {
    assert(expr.operands().size()==2);
    for(auto & op : expr.operands())
      typecheck_expr(op);

    expr.type()=expr.op0().type();
  }
  else if(expr.id()==ID_not)
  {
    assert(expr.operands().size()==1);
    typecheck_expr(expr.op0());
    expr.type()=expr.op0().type();
  }
  else if(expr.id()==ID_symbol)
  {
    symbol_exprt &symbol_expr=to_symbol_expr(expr);
    irep_idt identifier=symbol_expr.get_identifier();
    
    // look up in symbol table
    irep_idt full_identifier=
      id2string(module_symbol->name)+"."+
      id2string(to_lower(identifier));

    symbol_tablet::symbolst::const_iterator s_it=
      symbol_table.symbols.find(full_identifier);
    
    if(s_it==symbol_table.symbols.end())
    {
      error() << "symbol `" << identifier << "' not found"
              << eom;
      throw 0;
    }

    symbol_expr.set_identifier(full_identifier);
    symbol_expr.type()=s_it->second.type;
  }
  else if(expr.id()==ID_constant)
  {
    irep_idt type=expr.type().id();
    if(type==ID_char)
    {
    }
    else if(type==ID_natural)
    {
    }
    else
      throw "unexpected constant of type: "+id2string(type);
  }
  else if(expr.id()==ID_equal || expr.id()==ID_notequal ||
          expr.id()==ID_le || expr.id()==ID_ge ||
          expr.id()==ID_lt || expr.id()==ID_gt)
  {
    assert(expr.operands().size()==2);
    
    typecheck_expr(expr.op0());
    typecheck_expr(expr.op1());
  
    // result is always boolean
    expr.type()=bool_typet();
  }
  else
    throw "unexpected expression: "+expr.id_string();
}

/*******************************************************************\

Function: vhdl_typecheckt::convert_to_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_typecheckt::convert_to_type(exprt &expr, const typet &type)
{
  if(expr.type()==type) return; // already done

  if(expr.id()==ID_constant)
  {
    //const irep_idt &value=to_constant_expr(expr).get_value();

    if(type.id()==ID_bool)
    {
    }
  }

  expr=typecast_exprt(expr, type);
}

/*******************************************************************\

Function: vhdl_typecheckt::typecheck_code_assert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_typecheckt::typecheck_code_assert(codet &code)
{
  assert(code.operands().size()==3);
  
  // op0 is the assertion
  typecheck_expr(code.op0());
  convert_to_type(code.op0(), bool_typet());

  // op1 must be a string (the report) or nil
  if(code.op1().is_nil())
  {
  }
  else if(code.op1().id()==ID_constant &&
          code.op1().type().id()==ID_string)
  {
  }
  else
  {
    //message_location(code.op1());
    error() << "report clause expects string argument" << eom;
    throw 0;
  }

  // op2 is the severity level or nil
  if(code.op2().is_nil())
  {
  }
}

/*******************************************************************\

Function: vhdl_typecheckt::typecheck_code_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_typecheckt::typecheck_code_assign(codet &code)
{
  typecheck_expr(code.op0());
  typecheck_expr(code.op1());
  convert_to_type(code.op1(), code.op0().type());
}

/*******************************************************************\

Function: vhdl_typecheckt::typecheck_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_typecheckt::typecheck_type(typet &type)
{
  if(type.id()==ID_symbol)
  {
    const irep_idt identifier=to_lower(type.get(ID_identifier));
    if(identifier=="boolean")
    {
      source_locationt source_location=type.source_location();
      type=bool_typet();
      type.add_source_location()=source_location;
    }
    else
    {
      error() << "unknown type `"
              << type.get(ID_identifier) << "'" << eom;
      throw 0;
    }
  }
  else
  {
    error() << "unexpected type: " << type.id() << eom;
    throw 0;
  }
}

/*******************************************************************\

Function: vhdl_typecheckt::typecheck_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_typecheckt::typecheck_code(codet &code)
{
  irep_idt statement=code.get_statement();
  
  if(statement==ID_assert)
    typecheck_code_assert(code);
  else if(statement==ID_assign)
    typecheck_code_assign(code);
  else if(statement==ID_continuous_assign)
  {
    typecheck_expr(code.op0());
    typecheck_expr(code.op1());
    convert_to_type(code.op1(), code.op0().type());
  }
  else
    throw "unexpected statement: "+id2string(statement);
}

/*******************************************************************\

Function: vhdl_typecheckt::typecheck_architecture_body

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_typecheckt::typecheck_architecture_body(exprt &body)
{
  for(auto & it : body.operands())
  {
    if(it.id()==ID_process)
    {
      for(auto & it2 : it.operands())
      {
        typecheck_code(to_code(it2));
      }
    }
    else if(it.id()==ID_generate_if)
    {
      throw "generate_if yet to be impleneted";
    }
    else if(it.id()==ID_generate_for)
    {
      throw "generate_for yet to be impleneted";
    }
    else if(it.id()==ID_continuous_assign)
    {
      throw "continous assignment yet to be implemented";
    }
    else
      throw "unexpected item in architecture body: "+it.id_string();
  }
}

/*******************************************************************\

Function: vhdl_typecheckt::typecheck_architecture

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_typecheckt::typecheck_architecture(
  const vhdl_parse_treet::itemt &item)
{
  // create symbol

  symbolt symbol;
  
  symbol.mode=ID_VHDL;
  symbol.name="vhdl::"+id2string(module_name);
  symbol.type=typet(ID_module);
  symbol.base_name=module_name;
  symbol.pretty_name=module_name;
  symbol.module=symbol.name;
  symbol.mode="VHDL";

  // put symbol in symbol_table

  symbolt *new_symbol;

  if(symbol_table.move(symbol, new_symbol))
  {
    error() << "duplicate definition of module " 
            << symbol.base_name << eom;
    throw 0;
  }
  
  module_symbol=new_symbol;
  
  irept entity=item.find(ID_entity);
  irept decl=item.find(ID_decl);
  exprt body=static_cast<const exprt &>(item.find(ID_body));
  
  typecheck_architecture_entity(entity);
  typecheck_architecture_decl(decl);
  typecheck_architecture_body(body);
  
  new_symbol->value.id(ID_module);
  new_symbol->value.set(ID_body, body);
}

/*******************************************************************\

Function: vhdl_typecheckt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_typecheckt::operator()()
{
  // find the module in the parse tree
  
  try
  {
    for(const auto & item : parse_tree.items)
      if(item.is_architecture() &&
         module_name==item.get_pretty_name())
      {
        typecheck_architecture(item);
        return false;
      }
  }
  catch(...)
  {
  }
  
  return true;
}

/*******************************************************************\

Function: vhdl_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_typecheck(
  const vhdl_parse_treet &parse_tree,
  symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  return vhdl_typecheckt(
    parse_tree, module, symbol_table, message_handler)();
}

