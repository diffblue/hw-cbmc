/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ctype.h>
#include <cstdlib>

#include <iostream>

#include <util/arith_tools.h>
#include <util/location.h>
#include <util/expr_util.h>
#include <util/simplify_expr.h>
#include <util/namespace.h>
#include <util/prefix.h>
#include <util/i2string.h>
#include <util/std_expr.h>

#include "expr2verilog.h"
#include "verilog_expr.h"
#include "verilog_typecheck_expr.h"
#include "vtype.h"

/*******************************************************************\

Function: verilog_typecheck_exprt::propagate_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::propagate_type(
  exprt &expr,
  const typet &type)
{
  if(expr.type()==type)
    return;

  vtypet vt_from=vtypet(expr.type());
  vtypet vt_to  =vtypet(type);

  if(!vt_from.is_other() && !vt_to.is_other() &&
     expr.has_operands())
  {
    // arithmetic
    
    if(expr.id()==ID_plus ||
       expr.id()==ID_minus ||
       expr.id()==ID_mult || 
       expr.id()==ID_div || 
       expr.id()==ID_unary_minus ||
       expr.id()==ID_unary_plus)
    {
      if(type.id()!=ID_bool)
      {
        Forall_operands(it, expr)
          propagate_type(*it, type);

        expr.type()=type;

        return;
      }
    }
    else if(expr.id()==ID_bitand  ||
            expr.id()==ID_bitor   ||
            expr.id()==ID_bitnand ||
            expr.id()==ID_bitnor  ||
            expr.id()==ID_bitxor  ||
            expr.id()==ID_bitxnor ||
            expr.id()==ID_bitnot)
    {
      Forall_operands(it, expr)
        propagate_type(*it, type);

      expr.type()=type;

      if(type.id()==ID_bool)
      {
        if(expr.id()==ID_bitand)
          expr.id(ID_and);
        else if(expr.id()==ID_bitor)
          expr.id(ID_or);
        else if(expr.id()==ID_bitnand)
          expr.id(ID_nand);
        else if(expr.id()==ID_bitnor)
          expr.id(ID_nor);
        else if(expr.id()==ID_bitxor)
          expr.id(ID_xor);
        else if(expr.id()==ID_bitxnor)
          expr.id(ID_xnor);
        else if(expr.id()==ID_bitnot)
          expr.id(ID_not);
      }

      return;
    }
    else if(expr.id()==ID_if)
    {
      if(expr.operands().size()==3)
      {
        propagate_type(expr.op1(), type);
        propagate_type(expr.op2(), type);

        expr.type()=type;
        return;
      }
    }
    else if(expr.id()==ID_shl) // does not work with shr
    {
      if(expr.operands().size()==2)
      {
        propagate_type(expr.op0(), type);
        // not applicable to second operand

        expr.type()=type;
        return;
      }
    }
    else if(expr.id()==ID_constraint_select_one)
    {
      expr.type()=type;

      Forall_operands(it, expr)
        propagate_type(*it, type);

      return;
    }
  }

  typecast(expr, type);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::no_bool

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::no_bool(exprt &expr)
{
  typet new_type(ID_unsignedbv);
  new_type.set(ID_width, 1);

  Forall_operands(it, expr)
    if(it->type().id()==ID_bool)
      it->make_typecast(new_type);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::convert_expr(exprt &expr)
{
  // variable number of operands

  if(expr.id()==ID_event)
  {
    expr.type()=typet(ID_bool);

    Forall_operands(it, expr)
      convert_expr(*it);
  }
  else if(expr.id()==ID_concatenation)
  {
    if(expr.operands().size()==0)
    {
      err_location(expr);
      str << "concatenation expected to have at least one operand";
      throw 0;
    }
    
    unsigned width=0;
    bool has_verilogbv=false;

    Forall_operands(it, expr)
    {
      convert_expr(*it);

      if(it->type().id()==ID_array)
      {
        err_location(*it);
        throw "array type not allowed here";
      }
      else if(it->type().id()==ID_integer)
      {
        err_location(*it);
        throw "integer type not allowed here";
      }
      else if(it->type().id()==ID_verilogbv)
      {
        has_verilogbv=true;
      }

      width+=get_width(*it);
    }

    expr.type()=typet(has_verilogbv?ID_verilogbv:ID_unsignedbv);
    expr.type().set(ID_width, width);
    
    // eliminate { x }
    if(expr.operands().size()==1)
    {
      exprt tmp=expr.op0();
      expr.swap(tmp);
    }
  }
  else if(expr.id()==ID_function_call)
  {
    convert_expr_function_call(to_function_call_expr(expr));
  }
  else if(expr.id()==ID_constraint_select_one)
  {
    convert_constraint_select_one(expr);
  }
  else
  {
    unsigned no_op;

    if(!expr.has_operands())
      no_op=0;
    else
      no_op=expr.operands().size();

    switch(no_op)
    {
     case 0: convert_nullary_expr(expr); break;
     case 1: convert_unary_expr  (expr); break;
     case 2: convert_binary_expr (expr); break;
     case 3: convert_trinary_expr(expr); break;
     default:
      err_location(expr);
      str << "no conversion for expression " << expr;
      throw 0;
    }
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_expr_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::convert_expr_function_call(
  function_call_exprt &expr)
{
  // arguments
  exprt::operandst &arguments=expr.arguments();
  
  Forall_expr(it, arguments)
    convert_expr(*it);
  
  if(expr.function().id()!=ID_symbol)
  {
    err_location(expr);
    throw "expected symbol as function argument";
  }
    
  symbol_exprt &f_op=to_symbol_expr(expr.function());
  
  // built-in functions
  const irep_idt &identifier=f_op.get_identifier();
  
  if(has_prefix(id2string(identifier), "$"))
    return convert_system_function(identifier, expr);

  std::string full_identifier=
    id2string(module_identifier)+"."+id2string(identifier);

  const symbolt *symbol;
  if(lookup(full_identifier, symbol))
  {
    err_location(f_op);
    str << "unknown function `" << identifier << "'";
    throw 0;
  }

  if(symbol->type.id()!=ID_code)
  {
    err_location(f_op);
    str << "expected function name";
    throw 0;
  }

  const code_typet &code_type=to_code_type(symbol->type);
  
  f_op.type()=code_type;
  f_op.set(ID_identifier, full_identifier);
  expr.type()=code_type.return_type();
  
  if(code_type.return_type().id()==ID_empty)
  {
    err_location(f_op);
    throw "expected function, but got task";
  }

  // check arguments
  const code_typet::argumentst &argument_types=code_type.arguments();

  if(argument_types.size()!=arguments.size())
  {
    err_location(expr);
    throw "wrong number of arguments";
  }

  for(unsigned i=0; i<arguments.size(); i++)
    propagate_type(arguments[i], argument_types[i].type());
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_constraint_select_one

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::convert_constraint_select_one(exprt &expr)
{
  if(expr.operands().size()<2)
  {
    err_location(expr);
    str << "constraint_select_one takes at least two operands";
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_system_function

  Inputs:

 Outputs:

 Purpose: Takes care of functions that start with $

\*******************************************************************/

void verilog_typecheck_exprt::convert_system_function(
  const irep_idt &identifier,
  function_call_exprt &expr)
{
  exprt::operandst &arguments=expr.arguments();

  if(identifier=="$signed")
  {
    // this is a type cast
    if(arguments.size()!=1)
    {
      err_location(expr);
      str << "$signed takes one argument";
      throw 0;
    }
    
    exprt &argument=arguments.front();
    
    if(argument.type().id()==ID_signedbv)
    {
      // remove
      exprt tmp=argument;
      expr.swap(tmp);
    }
    else if(argument.type().id()==ID_unsignedbv)
    {
      exprt tmp(ID_typecast, argument.type());
      tmp.type().id(ID_signedbv);
      tmp.move_to_operands(argument);
      tmp.location()=expr.location();
      expr.swap(tmp);
    }
    else if(argument.type().id()==ID_bool)
    {
      exprt tmp(ID_typecast, typet(ID_signedbv));
      tmp.type().set(ID_width, 2);
      tmp.move_to_operands(argument);
      tmp.location()=expr.location();
      expr.swap(tmp);
    }
    else
    {
      err_location(expr);
      str << "$signed takes an unsigned bit-vector as argument, but got "
          << to_string(argument.type());
      throw 0;
    }
  }
  else if(identifier=="$unsigned")
  {
    // this is a type cast
    if(arguments.size()!=1)
    {
      err_location(expr);
      str << "$unsigned takes one argument";
      throw 0;
    }
    
    exprt &argument=arguments.front();

    if(argument.type().id()==ID_unsignedbv)
    {
      // remove
      exprt tmp=argument;
      expr.swap(tmp);
    }
    else if(argument.type().id()==ID_signedbv)
    {
      exprt tmp(ID_typecast, argument.type());
      tmp.type().id(ID_unsignedbv);
      tmp.move_to_operands(argument);
      tmp.location()=expr.location();
      expr.swap(tmp);
    }
    else if(argument.type().id()==ID_bool)
    {
      exprt tmp(ID_typecast, typet(ID_unsignedbv));
      tmp.type().set(ID_width, 1);
      tmp.move_to_operands(argument);
      tmp.location()=expr.location();
      expr.swap(tmp);
    }
    else
    {
      err_location(expr);
      str << "$unsigned takes an unsigned bit-vector as argument, but got "
          << to_string(argument.type());
      throw 0;
    }
  }
  else if(identifier=="$ND")
  {
    // this is something from VIS
    
    if(arguments.size()<1)
    {
      err_location(expr);
      str << "$ND takes at least one argument";
      throw 0;
    }
    
    if(arguments.size()==1)
    {
      // remove
      exprt tmp=arguments.front();
      expr.swap(tmp);
      return;
    }

    std::string identifier=
      id2string(module_identifier)+"::nondet::"+i2string(nondet_count++);

    typet type=arguments.front().type();

    exprt select_one(ID_constraint_select_one, type);
    select_one.operands()=arguments;
    
    expr.swap(select_one);
  }
  else
  {
    err_location(expr.function());
    str << "unknown system function `" << identifier << "'";
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_nullary_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::convert_nullary_expr(exprt &expr)
{
  if(expr.id()==ID_constant)
  {
    convert_constant(to_constant_expr(expr));
  }
  else if(expr.id()==ID_symbol)
  {
    convert_symbol(expr);
  }
  else if(expr.id()=="star-event")
  {
  }
  else
  {
    err_location(expr);
    str << "no conversion for no-operand expression " << expr;
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::convert_symbol(exprt &expr)
{
  const irep_idt &identifier=to_symbol_expr(expr).get_identifier();
  
  std::string full_identifier;

  // in a task or function? Try local ones first
  if(function_or_task_name!="")
  {
    full_identifier=
      id2string(function_or_task_name)+
      "."+id2string(identifier);
    
    const symbolt *symbol;
    if(!lookup(full_identifier, symbol))
    { // found!
      expr.type()=symbol->type;
      expr.set(ID_identifier, full_identifier);
      return;
    }
  }
  
  full_identifier=
    id2string(module_identifier)+"."+id2string(identifier);
  
  const symbolt *symbol;
  if(!lookup(full_identifier, symbol))
  { 
    // found! This is a constant
    if(symbol->type.id()==ID_genvar)
    {
      mp_integer int_value;

      genvar_value(identifier, int_value);

      if(int_value<0)
      {
        err_location(expr);
        str << "invalid genvar value";
        throw 0;
      }
      
      unsigned bits=integer2long(address_bits(int_value+1));
      locationt location=expr.location();

      expr=exprt(ID_constant, typet(ID_unsignedbv));
      expr.location()=location;
      expr.type().set(ID_width, bits);
      expr.set(ID_value, integer2binary(int_value, bits));
    }
    else
    {
      expr.type()=symbol->type;
      expr.set(ID_identifier, full_identifier);
    }
  }
  else if(!implicit_wire(identifier, symbol))
  {
    err_location(expr);
    str << "implicit definition of wire "
        << full_identifier;
    warning();
    expr.type()=symbol->type;
    expr.set(ID_identifier, symbol->name);
  }
  else
  {
    err_location(expr);
    str << "unknown identifier " << identifier;
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_hierarchical_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::convert_hierarchical_identifier(
  hierarchical_identifier_exprt &expr)
{
  convert_expr(expr.op0());

  if(expr.op0().id()!=ID_symbol)
  {
    err_location(expr);
    throw "expected symbol on lhs of `.'";
  }

  if(expr.op0().type().id()!=ID_module_instance)
  {
    err_location(expr);
    str << "expected module instance on lhs of `.', but got `"
        << to_string(expr.op0().type()) << "'";
    throw 0;
  }
  
  const irep_idt &lhs_identifier=expr.op0().get(ID_identifier);

  // figure out which module this is
  const symbolt *module_instance_symbol;
  if(lookup(lhs_identifier, module_instance_symbol))
  {
    err_location(expr);
    str << "failed to find module instance `"
        << lhs_identifier << "' on lhs of `.'";
    throw 0;
  }

  const irep_idt &module=module_instance_symbol->value.get(ID_module);

  if(expr.op1().id()!=ID_symbol)
  {
    err_location(expr);
    str << "expected symbol on rhs of `.', but got `"
        << to_string(expr.op1()) << "'";
    throw 0;
  }

  const irep_idt &rhs_identifier=expr.op1().get(ID_identifier);
  
  std::string full_identifier=
    id2string(module)+"."+id2string(rhs_identifier);
  
  const symbolt *symbol;
  if(!lookup(full_identifier, symbol))
  {
    if(symbol->type.id()==ID_genvar)
    {
      err_location(expr);
      str << "genvars must not be used in hierarchical identifiers";
      throw 0;
    }
    else
    {
      expr.type()=symbol->type;
    }
  }
  else
  {
    err_location(expr);
    str << "identifier `" << rhs_identifier
        << "' not found in `" << module << "'" << std::endl;
    str << "full identifier: " << full_identifier;
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::convert_constant(constant_exprt &expr)
{
  if(expr.type().id()==ID_string)
  {
    exprt new_expr;
    const std::string &value=expr.get_string(ID_value);

    new_expr.type()=typet(ID_unsignedbv);
    new_expr.type().set(ID_width, value.size()*8);

    std::string new_value;

    for(unsigned i=0; i<value.size(); i++)
      for(unsigned bit=0; bit<8; bit++)
      {
        bool b=(value[i]&(1<<bit));
        new_value=(b?"1":"0")+new_value;
      }

    new_expr.set(ID_value, new_value);
    
    expr.swap(new_expr);
    return;
  }
  else if(expr.type().id()==ID_unsignedbv ||
          expr.type().id()==ID_signedbv)
  {
    // done already
    return;
  }

  // first, get rid of whitespace and underscores
  // and make everything lower case

  const std::string &value=expr.get_string(ID_value);
  expr.set("#verilog_value", value);
  
  std::string rest;

  for(unsigned i=0; i<value.size(); i++)
  {
    char ch=value[i];
    if(!isspace(ch) && ch!='_') rest+=tolower(ch);
  }

  // check representation

  std::string::size_type pos=rest.find('\'');
  unsigned bits=0;
  bool bits_given(false);

  if(pos!=std::string::npos) // size given?
  {
    if(rest[0]!='\'')
    {
      bits=atoi(rest.c_str());
      bits_given=true;

      if(bits==0)
      {
        err_location(expr);
        throw "zero-length bit vector not allowed";
      }
    }

    rest=rest.substr(pos+1);
  }

  unsigned base=10;

  // base given?

  if(rest!="")
  {
    switch(rest[0])
    {
     case 'b': base=2;  rest.erase(0, 1); break;
     case 'd': base=10; rest.erase(0, 1); break;
     case 'h': base=16; rest.erase(0, 1); break;
     case 'o': base=8;  rest.erase(0, 1); break;
     default:  base=10;
    }
  }

  // check for z/x

  bool other=false;

  for(unsigned i=0; i<rest.size(); i++)
    if(rest[i]=='?' || rest[i]=='z' || rest[i]=='x')
      other=true;

  if(other) // z/x/? found
  {
    // expand bits

    std::string full_value=rest;
    std::string bit_value;

    switch(base)
    {
    case 2:
      bit_value=full_value;
      break;

    case 8:
      for(unsigned i=0; i<full_value.size(); i++)
      {
        switch(full_value[i])
        {
         case '0': bit_value+="000"; break;
         case '1': bit_value+="001"; break;
         case '2': bit_value+="010"; break;
         case '3': bit_value+="011"; break;
         case '4': bit_value+="100"; break;
         case '5': bit_value+="101"; break;
         case '6': bit_value+="110"; break;
         case '7': bit_value+="111"; break;
         case 'x': bit_value+="xxx"; break;
         case 'z': bit_value+="zzz"; break;
        }
      }
      break;         

    case 16:
      for(unsigned i=0; i<full_value.size(); i++)
      {
        switch(full_value[i])
        {
         case '0': bit_value+="0000"; break;
         case '1': bit_value+="0001"; break;
         case '2': bit_value+="0010"; break;
         case '3': bit_value+="0011"; break;
         case '4': bit_value+="0100"; break;
         case '5': bit_value+="0101"; break;
         case '6': bit_value+="0110"; break;
         case '7': bit_value+="0111"; break;
         case '8': bit_value+="1000"; break;
         case '9': bit_value+="1001"; break;
         case 'a': bit_value+="1010"; break;
         case 'b': bit_value+="1011"; break;
         case 'c': bit_value+="1100"; break;
         case 'd': bit_value+="1101"; break;
         case 'e': bit_value+="1110"; break;
         case 'f': bit_value+="1111"; break;
         case 'x': bit_value+="xxxx"; break;
         case 'z': bit_value+="zzzz"; break;
        }
      }
      break;         

    default:
      err_location(expr);
      str << "cannot convert " << value;
      throw 0;
    }

    std::string fvalue;

    if(bits_given)
    {
      fvalue=bit_value;

      if(fvalue.size()>bits)
        fvalue.erase(0, fvalue.size()-bits); // cut off...
      else if(fvalue.size()<bits)
      {
        // extend
        char ext='0';

        if(fvalue.size()!=0 && (fvalue[0]=='x' || fvalue[0]=='z'))
          ext=fvalue[0];

        // add missing bits
        fvalue=std::string(bits-fvalue.size(), ext)+fvalue;
      }
    }
    else
    {
      fvalue=bit_value;
      bits=fvalue.size();
    }

    expr.type()=typet(ID_verilogbv);
    expr.type().set(ID_width, bits);
    expr.set(ID_value, fvalue);
    expr.set(ID_C_little_endian, true);
  }
  else
  {
    mp_integer int_value=string2integer(rest, base);
    
    if(!bits_given)
    {
      bits=integer2long(address_bits(int_value+1));
      // we do a 32-bit minimum
      if(bits<32) bits=32;
    }

    expr.type()=typet(ID_unsignedbv);
    expr.type().set(ID_width, bits);
    expr.set(ID_value, integer2binary(int_value, bits));
    expr.set(ID_C_little_endian, true);
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_const_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::convert_const_expression(
  const exprt &expr,
  mp_integer &value)
{
  exprt tmp(expr);

  convert_expr(tmp);
  follow_macros(tmp);

  // this could be large
  propagate_type(tmp, integer_typet());
  
  simplify(tmp, ns());

  if(tmp.is_true())
    value=1;
  else if(tmp.is_false())
    value=0;
  else if(to_integer(tmp, value))
  {
    err_location(expr);
    str << "expected constant expression, but got "
        << to_string(tmp);
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::is_const_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_typecheck_exprt::is_const_expression(
  const exprt &expr,
  mp_integer &value)
{
  exprt tmp(expr);

  convert_expr(tmp);
  follow_macros(tmp);

  simplify(tmp, ns());

  if(tmp.is_true())
  {
    value=1;
    return true;
  }
  else if(tmp.is_false())
  {
    value=0;
    return true;
  }
  else if(!to_integer(tmp, value))
  {
    return true;
  }

  return false;
}

/*******************************************************************\

Function: verilog_typecheck_exprt::typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::typecast(
  exprt &expr,
  const typet &dest_type)
{
  if(dest_type.id()==irep_idt())
    return;

  if(expr.type()==dest_type)
    return;

  if(dest_type.id()==ID_integer)
  {
    if(expr.is_constant())
    {
      locationt location=expr.location();
      mp_integer value;

      if(to_integer(expr, value))
        throw "failed to convert integer constant";

      expr=from_integer(value, dest_type);
      expr.location()=location;
      return;
    }

    if(expr.type().id()==ID_bool ||
       expr.type().id()==ID_unsignedbv ||
       expr.type().id()==ID_signedbv ||
       expr.type().id()==ID_integer)
    {
      expr.make_typecast(dest_type);
      return;
    }
  }

  if(expr.type().id()==ID_integer)
  {
    // from integer to s.th. else
    if(dest_type.id()==ID_bool)
    {
      // do not use typecast here
      // we actually only want the lowest bit
      unsignedbv_typet tmp_type;
      tmp_type.set_width(1);
      exprt tmp(ID_extractbit, bool_typet());
      exprt no_expr=from_integer(0, integer_typet());
      tmp.copy_to_operands(typecast_exprt(expr, tmp_type), no_expr);
      expr.swap(tmp);
      return;
    }
    else if(dest_type.id()==ID_unsignedbv ||
            dest_type.id()==ID_signedbv ||
            dest_type.id()==ID_verilogbv)
    {
      expr.make_typecast(dest_type);
      return;
    }
  }
  else if(expr.type().id()==ID_bool ||
          expr.type().id()==ID_unsignedbv ||
          expr.type().id()==ID_signedbv ||
          expr.type().id()==ID_verilogbv)
  {
    if(dest_type.id()==ID_bool)
    {
      // do not use typecast here
      // we actually only want the lowest bit

      if(expr.is_constant() &&
         expr.type().id()==ID_unsignedbv)
      {
        const std::string &value=expr.get_string(ID_value);
        // least significant bit is last
        assert(value.size()!=0);
        expr.make_bool(value[value.size()-1]=='1');
        return;
      }

      exprt tmp(ID_extractbit, bool_typet());
      exprt no_expr=from_integer(0, integer_typet());
      tmp.move_to_operands(expr, no_expr);
      expr.swap(tmp);
      return;
    }
    else if(dest_type.id()==ID_unsignedbv ||
            dest_type.id()==ID_signedbv)
    {
      if(expr.is_true() || expr.is_false())
        expr=from_integer(expr.is_true()?1:0, dest_type);
      else if(expr.is_constant())
      {
        mp_integer i;
        if(to_integer(expr, i))
          expr.make_typecast(dest_type);
        else
          expr=from_integer(i, dest_type);
      }
      else
        expr.make_typecast(dest_type);

      return;
    }
    else if(dest_type.id()==ID_verilogbv)
    {
      expr.make_typecast(dest_type);
      return;
    }
  }

  err_location(expr);
  str << "failed to convert `" << to_string(expr.type()) 
      << "' to `" << to_string(dest_type) << "'";
  throw 0;
}

/*******************************************************************\

Function: verilog_typecheck_exprt::make_boolean

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::make_boolean(exprt &expr)
{
  if(expr.type().id()!=ID_bool)
  {
    mp_integer value;
    if(!to_integer(expr, value))
      expr.make_bool(value!=0);
    else
      expr.make_typecast(bool_typet());
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_range

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::convert_range(
  const exprt &range,
  mp_integer &msb,
  mp_integer &lsb)
{
  if(range.operands().size()!=2)
  {
    err_location(range);
    str << "part_select expected to have two operands" << std::endl;
    str << range;
    throw 0;
  }

  convert_const_expression(range.op0(), msb);
  convert_const_expression(range.op1(), lsb);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::convert_type(
  const irept &src,
  typet &dest)
{
  if(src.is_nil() || src.id()==ID_reg)
  {
    // it's just a bit
    dest=typet(ID_bool);
    return;
  }
  
  if(src.id()==ID_range)
  {
    mp_integer msb, lsb;

    convert_range(static_cast<const exprt &>(src), msb, lsb);

    bool little_endian=(lsb<=msb);

    mp_integer width=(little_endian?msb-lsb:lsb-msb)+1;
    mp_integer offset=little_endian?lsb:msb;
    
    // let's look at the subtype
    const irept &subtype=src.find(ID_subtype);
    
    if(subtype.is_nil() ||
       subtype.id()==ID_signed ||
       subtype.id()==ID_unsigned)
    {
      // we have a bit-vector type

      dest=typet(subtype.id()==ID_signed?ID_signedbv:ID_unsignedbv);

      dest.set(ID_C_location, src.find(ID_C_location));
      dest.set(ID_width, integer2string(width));
      dest.set(ID_C_little_endian, little_endian);
      dest.set(ID_C_offset, integer2string(offset));
    }
    else
    {
      // we have an array, and do a recursive call
      dest=typet(ID_array);
      dest.set(ID_size, from_integer(width, integer_typet()));
      dest.set(ID_C_location, src.find(ID_C_location));
      dest.set(ID_offset, from_integer(offset, integer_typet()));
      convert_type(subtype, dest.subtype());
    }
  }
  else
  {
    err_location(src);
    throw "unexpected type: `"+src.id_string()+"'";
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::tc_binary_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::tc_binary_expr(
  const exprt &expr,
  exprt &op0, exprt &op1)
{
  const typet new_type=max_type(op0.type(), op1.type());
  
  if(new_type.is_nil())
  {
    err_location(expr);
    str << "expected operands of compatible type but got:" << std::endl;
    str << "  " << to_string(op0.type()) << std::endl
        << "  " << to_string(op1.type());
    throw 0;
  }

  propagate_type(op0, new_type);
  propagate_type(op1, new_type);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::max_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet verilog_typecheck_exprt::max_type(
  const typet &t0,
  const typet &t1)
{
  if(t0==t1) return t0;

  vtypet vt0=vtypet(t0);
  vtypet vt1=vtypet(t1);

  if(vt0.is_other() || vt1.is_other())
    return static_cast<const typet &>(get_nil_irep());

  // If one of the operands is an integer, we return the
  // other type. This may be too small! The standard says
  // one needs 32 bits.
  
  if(vt0.is_integer())
    return t1;
  else if(vt1.is_integer())
    return t0;
  else if(vt0.is_verilogbv() || vt1.is_verilogbv())
  {
    // we might need signed and unsigned verilogbv-s
    typet result(ID_verilogbv);
    result.set(ID_width, std::max(vt0.get_width(), vt1.get_width()));
    return result;
  }
  else if(vt0.is_unsigned() && vt1.is_unsigned())
    return (vt0.get_width()>=vt1.get_width())?t0:t1;
  else if(vt0.is_signed() || vt1.is_signed())
  {
    signedbv_typet new_type;
    new_type.set_width(std::max(vt0.get_width(), vt1.get_width()));
    return new_type;
  }
  else if(vt0.is_bool() && (vt1.is_unsigned() || vt1.is_signed()))
    return t1;
  else if(vt1.is_bool() && (vt0.is_unsigned() || vt0.is_signed()))
    return t0;
  else
  {
    str << "t0: " << t0.pretty() << std::endl
        << "t1: " << t1.pretty() << std::endl;
    throw "unexpected pair of types";
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::tc_binary_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::tc_binary_expr(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator " << expr.id_string()
        << " takes two operands";
    throw 0;
  }

  tc_binary_expr(expr, expr.op0(), expr.op1());
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_unary_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::convert_unary_expr(exprt &expr)
{
  if(expr.id()==ID_not)
  {
    expr.type()=typet(ID_bool);
    convert_expr(expr.op0());
    make_boolean(expr.op0());
  }
  else if(expr.id()==ID_reduction_or  || expr.id()==ID_reduction_and ||
          expr.id()==ID_reduction_nor || expr.id()==ID_reduction_nand ||
          expr.id()==ID_reduction_xor || expr.id()==ID_reduction_xnor)
  {
    expr.type()=typet(ID_bool);
    convert_expr(expr.op0());
  }
  else if(expr.id()==ID_unary_minus ||
          expr.id()==ID_unary_plus)
  {
    convert_expr(expr.op0());
    no_bool(expr);
    expr.type()=expr.op0().type();
  }
  else
  {
    convert_expr(expr.op0());
    expr.type()=expr.op0().type();

    // check boolean operators

    if(expr.type().id()==ID_bool && expr.id()==ID_bitnot)
      expr.id(ID_not);
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_binary_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::convert_binary_expr(exprt &expr)
{
  if(expr.id()==ID_extractbit)
  {
    exprt &op0=expr.op0();

    convert_expr(op0);

    if(op0.type().id()==ID_array)
    {
      exprt &op1=expr.op1();
      convert_expr(op1);
      typet _index_type=index_type(op0.type());

      if(_index_type!=op1.type())
      {
        mp_integer i;
        if(!to_integer(op1, i))
          op1=from_integer(i, _index_type);
        else if(op1.is_true() || op1.is_false())
          op1=from_integer(op1.is_true()?1:0, _index_type);
        else
          expr.op1().make_typecast(_index_type);
      }

      expr.type()=op0.type().subtype();
      expr.id(ID_index);
    }
    else
    {
      unsigned width=get_width(op0.type());
      unsigned offset=atoi(op0.type().get(ID_C_offset).c_str());

      mp_integer op1;

      if(is_const_expression(expr.op1(), op1))
      {
        if(op1<offset)
        {
          err_location(expr);
          str << "bit selection below lower bound: " << op1 << "<" << offset;
          throw 0;
        }

        if(op1>=width+offset)
        {
          err_location(expr); 
          str << "bit selection out of range: " 
              << op1 << ">=" << (width+offset);
          throw 0;
        }

        op1-=offset;

        expr.op1()=from_integer(op1, typet(ID_natural));
      }
      else
      {
        convert_expr(expr.op1());
      }

      expr.type()=typet(ID_bool);
    }
  }
  else if(expr.id()==ID_replication)
  {
    exprt &op1=expr.op1();

    convert_expr(op1);

    if(op1.type().id()==ID_array)
    {
      err_location(op1);
      throw "array type not allowed here";
    } 

    unsigned width=get_width(expr.op1().type());

    mp_integer op0;
    convert_const_expression(expr.op0(), op0);

    if(op0<0)
    {
      err_location(expr); 
      str << "number of replications must not be negative";
      throw 0;
    }

    {
      expr.op0()=from_integer(op0, typet(ID_natural));

      mp_integer new_width=op0*width;

      if(new_width==1)
        expr.type()=typet(ID_bool);
      else
      {
        expr.type()=typet(ID_unsignedbv);
        expr.type().set(ID_width, integer2string(new_width));
      }
    }
  }
  else if(expr.id()==ID_and || expr.id()==ID_or)
  {
    Forall_operands(it, expr)
    {
      convert_expr(*it);
      make_boolean(*it);
    }

    expr.type()=typet(ID_bool);
  }
  else if(expr.id()==ID_equal || expr.id()==ID_notequal)
  {
    expr.type()=typet(ID_bool);

    Forall_operands(it, expr)
      convert_expr(*it);

    tc_binary_expr(expr);
  }
  else if(expr.id()==ID_lt || expr.id()==ID_gt ||
          expr.id()==ID_le || expr.id()==ID_ge)
  {
    expr.type()=typet(ID_bool);

    Forall_operands(it, expr)
      convert_expr(*it);

    tc_binary_expr(expr);
    no_bool(expr);
  }
  else if(expr.id()==ID_shl)
  {
    mp_integer i;
    bool distance_is_const=
      is_const_expression(expr.op1(), i);
      
    // do *after* is_const_expression
    convert_expr(expr.op0());
    convert_expr(expr.op1());
    
    no_bool(expr);

    if(distance_is_const && i>=1)
    {
      // make wider as needed
      mp_integer width=mp_integer(get_width(expr.op0().type()))+i;
      typet new_type=expr.op0().type();
      new_type.set(ID_width, integer2string(width));
      expr.type()=new_type;
      propagate_type(expr.op0(), new_type);
    }
    else
    {
      no_bool(expr);
      expr.type()=expr.op0().type();
      // type is guessed for now
      // hopefully propagate_type will fix it
    }
  }
  else if(expr.id()==ID_shr)
  {
    // This is the >>> expression, which turns into ID_lshr or ID_ashr
    // depending on type of first operand.

    convert_expr(expr.op0());
    convert_expr(expr.op1());
    no_bool(expr);

    const typet &op0_type=expr.op0().type();

    if(op0_type.id()==ID_signedbv ||
       op0_type.id()==ID_integer)
      expr.id(ID_ashr);
    else
      expr.id(ID_lshr);
  }
  else if(expr.id()==ID_ashr)
  {
    // would only happen when re-typechecking, otherwise see above
    assert(0);
  }
  else if(expr.id()==ID_lshr)
  {
    // logical right shift >>
    convert_expr(expr.op0());
    convert_expr(expr.op1());
    no_bool(expr);
    expr.type()=expr.op0().type();
  }
  else if(expr.id()==ID_div || expr.id()==ID_mod)
  {
    Forall_operands(it, expr)
      convert_expr(*it);

    tc_binary_expr(expr);
    no_bool(expr);

    expr.type()=expr.op0().type();
  }
  else if(expr.id()==ID_hierarchical_identifier)
  {
    convert_hierarchical_identifier(to_hierarchical_identifier_expr(expr));
  }
  else
  {
    // type is guessed for now
    // hopefully propagate_type will fix it

    Forall_operands(it, expr)
      convert_expr(*it);

    tc_binary_expr(expr);

    if(expr.id()==ID_plus ||
       expr.id()==ID_minus ||
       expr.id()==ID_mult)
      no_bool(expr);

    expr.type()=expr.op0().type();

    // check Boolean operators

    if(expr.type().id()==ID_bool)
    {
      if(expr.id()==ID_bitand)
        expr.id(ID_and);
      else if(expr.id()==ID_bitor)
        expr.id(ID_or);
      else if(expr.id()==ID_bitxor)
        expr.id(ID_xor);
      else if(expr.id()==ID_bitxnor)
        expr.id(ID_equal);
      else if(expr.id()==ID_bitnand)
        expr.id(ID_nand);
      else if(expr.id()==ID_bitnor)
        expr.id(ID_nor);
    }
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_trinary_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::convert_trinary_expr(exprt &expr)
{
  if(expr.id()==ID_extractbits)
  {
    exprt &op0=expr.op0();

    convert_expr(op0);

    if(op0.type().id()==ID_array)
    {
      err_location(op0);
      throw "array type not allowed here";
    }

    unsigned width=get_width(op0.type());
    unsigned offset=atoi(op0.type().get(ID_C_offset).c_str());

    mp_integer op1, op2;

    convert_const_expression(expr.op1(), op1);
    convert_const_expression(expr.op2(), op2);

    if(op1<op2)
      std::swap(op1, op2);

    // now op1>=op2

    if(op2<offset)
    {
      err_location(expr); 
      str << "bit selection below offset";
      throw 0;
    }

    if(op1>=width+offset)
    {
      err_location(expr); 
      str << "bit selection out of range: " 
          << op1 << ">=" << (width+offset);
      throw 0;
    }

    op2-=offset;
    op1-=offset;

    expr.op1()=from_integer(op1, typet(ID_natural));
    expr.op2()=from_integer(op2, typet(ID_natural));
    
    expr.type()=typet(ID_unsignedbv);
    expr.type().set(ID_width, integer2long(op1-op2+1));
  }
  else if(expr.id()==ID_if)
  {
    convert_expr(expr.op0());
    make_boolean(expr.op0());
    convert_expr(expr.op1());
    convert_expr(expr.op2());

    tc_binary_expr(expr, expr.op1(), expr.op2());
    expr.type()=expr.op1().type();

    return;
  }
  else
  {
    err_location(expr);
    str << "no conversion for trinary expression " << expr;
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_typecheck(
  exprt &expr,
  const std::string &module_identifier,
  message_handlert &message_handler,
  const namespacet &ns)
{
  verilog_typecheck_exprt verilog_typecheck_expr(
    ns, module_identifier, message_handler);

  try
  {
    verilog_typecheck_expr.convert_expr(expr);
  }

  catch(int e)
  {
    verilog_typecheck_expr.error();
  }

  catch(const char *e)
  {
    verilog_typecheck_expr.error(e);
  }

  catch(const std::string &e)
  {
    verilog_typecheck_expr.error(e);
  }
  
  return verilog_typecheck_expr.get_error_found();
}
