/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_typecheck_expr.h"

#include <util/bitvector_expr.h>
#include <util/ebmc_util.h>
#include <util/expr_util.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include "expr2verilog.h"
#include "sva_expr.h"
#include "verilog_expr.h"
#include "verilog_types.h"
#include "vtype.h"

#include <algorithm>
#include <cctype>
#include <cstdlib>

/*******************************************************************\

Function: verilog_typecheck_exprt::hierarchical_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt
verilog_typecheck_exprt::hierarchical_identifier(irep_idt base_name) const
{
  const std::string named_block =
    named_blocks.empty() ? std::string() : id2string(named_blocks.back());

  if(function_or_task_name.empty())
    return id2string(module_identifier) + "." + named_block +
           id2string(base_name);
  else
    return id2string(function_or_task_name) + "." + named_block +
           id2string(base_name);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::enter_named_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::enter_named_block(const irep_idt &name)
{
  if(name!=irep_idt())
  {
    if(named_blocks.empty())
      named_blocks.push_back(id2string(name)+".");
    else
    {
      std::string new_id=
        id2string(named_blocks.back())+id2string(name)+".";
      named_blocks.push_back(new_id);
    }
  }
}

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
  auto &verilog_dest_type = type.get(ID_C_verilog_type);
  if(verilog_dest_type == ID_verilog_enum)
  {
    // IEEE 1800-2017 6.19.3: "a variable of type enum cannot be directly
    // assigned a value that lies outside the enumeration set unless an
    // explicit cast is used"
    if(
      expr.type().get(ID_C_verilog_type) != ID_verilog_enum ||
      expr.type().get(ID_C_identifier) != type.get(ID_C_identifier))
    {
      throw errort().with_location(expr.source_location())
        << "assignment to enum requires enum of the same type, but got "
        << to_string(expr.type());
    }
  }

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
       expr.id()==ID_power ||
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
        propagate_type(to_if_expr(expr).true_case(), type);
        propagate_type(to_if_expr(expr).false_case(), type);

        expr.type()=type;
        return;
      }
    }
    else if(expr.id()==ID_shl) // does not work with shr
    {
      // does not work with boolean
      if(type.id()!=ID_bool)
      {
        if(expr.operands().size()==2)
        {
          propagate_type(to_binary_expr(expr).op0(), type);
          // not applicable to second operand

          expr.type()=type;
          return;
        }
      }
    }
  }

  implicit_typecast(expr, type);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::no_bool_ops

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::no_bool_ops(exprt &expr)
{
  unsignedbv_typet new_type(1);

  Forall_operands(it, expr) if (it->type().id() == ID_bool) *it =
      typecast_exprt{*it, new_type};
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_expr_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_expr_rec(exprt expr)
{
  // variable number of operands

  if(expr.id()==ID_event)
  {
    expr.type()=bool_typet();

    Forall_operands(it, expr)
      convert_expr(*it);

    return expr;
  }
  else if(expr.id()==ID_concatenation)
  {
    if(expr.operands().size()==0)
    {
      throw errort().with_location(expr.source_location())
        << "concatenation expected to have at least one operand";
    }

    mp_integer width = 0;
    bool has_verilogbv=false;

    Forall_operands(it, expr)
    {
      convert_expr(*it);
      
      const typet &type=it->type();

      if(type.id()==ID_array)
      {
        throw errort().with_location(it->source_location())
          << "array type not allowed in concatenation";
      }
      else if(type.id() == ID_integer)
      {
        throw errort().with_location(it->source_location())
          << "integer type not allowed in concatenation";
      }
      else if(type.id()==ID_verilog_signedbv ||
              type.id()==ID_verilog_unsignedbv)
        has_verilogbv=true;

      width+=get_width(*it);
    }

    // Cocatenations are unsigned regardless of the operands
    // We cast all the signed operands to unsigned.
    for(auto &op : expr.operands())
    {
      if(op.type().id() == ID_signedbv || op.type().id() == ID_verilog_signedbv)
      {
        auto width = get_width(op);
        auto width_int = numeric_cast_v<std::size_t>(width);
        if(op.type().id() == ID_verilog_signedbv)
          op = typecast_exprt{op, verilog_unsignedbv_typet{width_int}};
        else
          op = typecast_exprt{op, unsignedbv_typet{width_int}};
      }
    }

    expr.type()=typet(has_verilogbv?ID_verilog_unsignedbv:ID_unsignedbv);
    expr.type().set(ID_width, integer2string(width));

    if(has_verilogbv)
    {
      Forall_operands(it, expr)
        if(it->type().id()!=ID_verilog_unsignedbv)
        {
          auto width_int = numeric_cast_v<std::size_t>(get_width(*it));
          *it = typecast_exprt{*it, verilog_unsignedbv_typet{width_int}};
        }
    }

    return expr;
  }
  else if(expr.id()==ID_function_call)
  {
    return convert_expr_function_call(to_function_call_expr(expr));
  }
  else
  {
    std::size_t no_op;

    if(!expr.has_operands())
      no_op=0;
    else
      no_op=expr.operands().size();

    switch(no_op)
    {
    // clang-format off
    case 0: return convert_nullary_expr(static_cast<const nullary_exprt &>(expr));
    case 1: return convert_unary_expr  (to_unary_expr(expr));
    case 2: return convert_binary_expr (to_binary_expr(expr));
    case 3: return convert_trinary_expr(to_ternary_expr(expr));
    // clang-format on
    default:
      throw errort().with_location(expr.source_location())
        << "no conversion for expression " << expr.id();
    }
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_expr_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_expr_function_call(
  function_call_exprt expr)
{
  // convert the arguments
  auto &arguments = expr.arguments();

  Forall_expr(it, arguments)
    convert_expr(*it);
  
  if(expr.function().id()!=ID_symbol)
  {
    throw errort().with_location(expr.source_location())
      << "expected symbol as function argument";
  }
    
  // built-in functions
  symbol_exprt &f_op=to_symbol_expr(expr.function());
  
  const irep_idt &identifier=f_op.get_identifier();
  
  if(expr.is_system_function_call())
    return convert_system_function(identifier, expr);

  std::string full_identifier=
    id2string(module_identifier)+"."+id2string(identifier);

  const symbolt *symbol;
  if(ns.lookup(full_identifier, symbol))
  {
    throw errort().with_location(f_op.source_location())
      << "unknown function `" << identifier << "'";
  }

  if(symbol->type.id()!=ID_code)
  {
    throw errort().with_location(f_op.source_location())
      << "expected function name";
  }

  const code_typet &code_type=to_code_type(symbol->type);
  
  f_op.type()=code_type;
  f_op.set(ID_identifier, full_identifier);
  expr.type()=code_type.return_type();
  
  if(code_type.return_type().id()==ID_empty)
  {
    throw errort().with_location(f_op.source_location())
      << "expected function, but got task";
  }

  // check arguments
  const code_typet::parameterst &parameter_types=code_type.parameters();

  if(parameter_types.size()!=arguments.size())
  {
    throw errort().with_location(expr.source_location())
      << "wrong number of arguments";
  }

  for(unsigned i=0; i<arguments.size(); i++)
    propagate_type(arguments[i], parameter_types[i].type());

  return std::move(expr);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::bits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::bits(const exprt &expr)
{
  auto width_opt = bits_rec(expr.type());

  if(!width_opt.has_value())
  {
    throw errort().with_location(expr.source_location())
      << "failed to determine number of bits of " << to_string(expr);
  }

  return from_integer(width_opt.value(), integer_typet());
}

/*******************************************************************\

Function: verilog_typecheck_exprt::bits_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::optional<mp_integer>
verilog_typecheck_exprt::bits_rec(const typet &type) const
{
  if(type.id() == ID_bool)
    return 1;
  else if(type.id() == ID_unsignedbv)
    return to_unsignedbv_type(type).get_width();
  else if(type.id() == ID_signedbv)
    return to_signedbv_type(type).get_width();
  else if(type.id() == ID_integer)
    return 32;
  else if(type.id() == ID_array)
  {
    auto &array_type = to_array_type(type);
    auto size_int =
      numeric_cast_v<mp_integer>(to_constant_expr(array_type.size()));
    auto element_bits_opt = bits_rec(array_type.element_type());
    if(element_bits_opt.has_value())
      return element_bits_opt.value() * size_int;
    else
      return {};
  }
  else if(type.id() == ID_struct)
  {
    auto &struct_type = to_struct_type(type);
    mp_integer sum = 0;
    for(auto &component : struct_type.components())
    {
      auto component_bits_opt = bits_rec(component.type());
      if(!component_bits_opt.has_value())
        return component_bits_opt.value();
      sum += component_bits_opt.value();
    }
    return sum;
  }
  else
    return {};
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_system_function

  Inputs:

 Outputs:

 Purpose: Takes care of functions that start with $

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_system_function(
  const irep_idt &identifier,
  function_call_exprt expr)
{
  exprt::operandst &arguments=expr.arguments();

  if(identifier=="$signed")
  {
    // this is a type cast
    if(arguments.size()!=1)
    {
      throw errort().with_location(expr.source_location())
        << "$signed takes one argument";
    }
    
    exprt &argument=arguments.front();
    
    if(argument.type().id()==ID_signedbv)
    {
      // remove
      return argument;
    }
    else if(argument.type().id()==ID_unsignedbv)
    {
      typet new_type = argument.type();
      new_type.id(ID_signedbv);
      typecast_exprt tmp{std::move(argument), std::move(new_type)};
      tmp.add_source_location() = expr.source_location();
      return std::move(tmp);
    }
    else if(argument.type().id()==ID_bool)
    {
      typecast_exprt tmp(argument, signedbv_typet(2));
      tmp.add_source_location()=expr.source_location();
      return std::move(tmp);
    }
    else
    {
      throw errort().with_location(expr.source_location())
        << "$signed takes an unsigned bit-vector as argument, but got `"
        << to_string(argument.type()) << '\'';
    }
  }
  else if(identifier=="$unsigned")
  {
    // this is a type cast
    if(arguments.size()!=1)
    {
      throw errort().with_location(expr.source_location())
        << "$unsigned takes one argument";
    }
    
    exprt &argument=arguments.front();

    if(argument.type().id()==ID_unsignedbv)
    {
      // remove
      return argument;
    }
    else if(argument.type().id()==ID_signedbv)
    {
      typecast_exprt tmp(argument, argument.type());
      tmp.type().id(ID_unsignedbv);
      tmp.add_source_location()=expr.source_location();
      return std::move(tmp);
    }
    else if(argument.type().id()==ID_bool)
    {
      typecast_exprt tmp(argument, unsignedbv_typet(1));
      tmp.add_source_location()=expr.source_location();
      return std::move(tmp);
    }
    else
    {
      throw errort().with_location(expr.source_location())
        << "$unsigned takes an unsigned bit-vector as argument, but got `"
        << to_string(argument.type()) << '\'';
    }
  }
  else if(identifier=="$ND")
  {
    // this is something from VIS
    
    if(arguments.size()<1)
    {
      throw errort().with_location(expr.source_location())
        << "$ND takes at least one argument";
    }

    expr.type() = arguments.front().type();
    return std::move(expr);
  }
  else if(identifier == "$bits")
  {
    if(arguments.size() != 1)
    {
      throw errort().with_location(expr.source_location())
        << "$bits takes one argument";
    }

    // The return type is integer.
    expr.type() = integer_typet();

    return std::move(expr);
  }
  else if(identifier=="$onehot") // SystemVerilog
  {
    if(arguments.size()!=1)
    {
      throw errort().with_location(expr.source_location())
        << "$onehot takes one argument";
    }
    
    // the meaning is 'exactly one bit is high'
    unary_predicate_exprt onehot(ID_onehot, arguments.front());
    onehot.add_source_location()=expr.source_location();

    return std::move(onehot);
  }
  else if(identifier=="$onehot0") // SystemVerilog
  {
    if(arguments.size()!=1)
    {
      throw errort().with_location(expr.source_location())
        << "$onehot takes one argument";
    }

    // the meaning is 'at most one bit is high'
    unary_predicate_exprt onehot0(ID_onehot0, arguments.front());
    onehot0.add_source_location()=expr.source_location();

    return std::move(onehot0);
  }
  else if(identifier == "$clog2") // Verilog-2005
  {
    if(arguments.size() != 1)
    {
      throw errort().with_location(expr.source_location())
        << "$clog2 takes one argument";
    }

    expr.type() = integer_typet();

    return std::move(expr);
  }
  else if(identifier == "$past")
  {
    if(arguments.size() == 0 || arguments.size() >= 4)
    {
      throw errort().with_location(expr.source_location())
        << "$past takes one to four arguments";
    }

    if(arguments.size() >= 2)
    {
      auto tmp = elaborate_constant_expression(arguments[1]);
      if(!tmp.is_constant())
      {
        throw errort().with_location(arguments[1].source_location())
          << "expected elaboration-time constant, but got `" << to_string(tmp)
          << '\'';
      }
    }

    expr.type() = arguments.front().type();

    return std::move(expr);
  }
  else if(
    identifier == "$stable" || identifier == "$rose" || identifier == "$fell" ||
    identifier == "$changed")
  {
    if(arguments.size() != 1 && arguments.size() != 2)
    {
      throw errort().with_location(expr.source_location())
        << identifier << " takes one or two arguments";
    }

    expr.type() = bool_typet();

    return std::move(expr);
  }
  else
  {
    throw errort().with_location(expr.function().source_location())
      << "unknown system function `" << identifier << "'";
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_nullary_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_nullary_expr(nullary_exprt expr)
{
  if(expr.id()==ID_constant)
  {
    return convert_constant(to_constant_expr(std::move(expr)));
  }
  else if(expr.id()==ID_symbol)
  {
    return convert_symbol(to_symbol_expr(std::move(expr)));
  }
  else if(expr.id()==ID_verilog_star_event)
  {
    return std::move(expr);
  }
  else if(expr.id()==ID_infinity)
  {
    // This is "$" and is used in cycle ranges.
    // We'll use the type 'natural'.
    expr.type() = natural_typet();
    return std::move(expr);
  }
  else if(expr.id() == ID_type)
  {
    // Used, e.g., for $bits
    expr.type() = convert_type(expr.type());
    return std::move(expr);
  }
  else
  {
    throw errort().with_location(expr.source_location())
      << "no conversion for no-operand expression " << expr.id();
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_symbol(symbol_exprt expr)
{
  const irep_idt &identifier = expr.get_identifier();

  std::string full_identifier;

  // in a task or function? Try local ones first
  if(function_or_task_name!="")
  {
    full_identifier=
      id2string(function_or_task_name)+
      "."+id2string(identifier);
    
    const symbolt *symbol;
    if(!ns.lookup(full_identifier, symbol))
    { // found!
      expr.type()=symbol->type;
      expr.set_identifier(full_identifier);
      return std::move(expr);
    }
  }
  
  std::string named_block;
  
  // try named blocks, beginning with inner one
  for(named_blockst::const_reverse_iterator
      it=named_blocks.rbegin();
      it!=named_blocks.rend();
      it++)
  {
    full_identifier=
      id2string(module_identifier)+"."+
      id2string(*it)+
      id2string(identifier);
    
    const symbolt *symbol;
    if(!ns.lookup(full_identifier, symbol))
    { // found!
      named_block=*it;
      break;
    }
  }
  
  full_identifier=
    id2string(module_identifier)+"."+
    named_block+
    id2string(identifier);

  const symbolt *symbol;
  if(!ns.lookup(full_identifier, symbol))
  { 
    // found!
    if(
      symbol->type.id() == ID_to_be_elaborated ||
      symbol->type.id() == ID_elaborating)
    {
      // A parameter, or enum. The type is elaborated recursively.
      elaborate_symbol_rec(symbol->name);
      expr.type() = symbol->type;
      expr.set_identifier(full_identifier);
      return std::move(expr);
    }
    else if(symbol->type.id() == ID_verilog_genvar)
    {
      // This must be a constant.
      mp_integer int_value = genvar_value(identifier);

      if(int_value<0)
      {
        throw errort().with_location(expr.source_location())
          << "invalid genvar value";
      }

      std::size_t bits = address_bits(int_value + 1);
      source_locationt source_location=expr.source_location();

      exprt result=from_integer(int_value, unsignedbv_typet(bits));
      result.add_source_location()=source_location;
      return result;
    }
    else
    {
      expr.type()=symbol->type;
      expr.set_identifier(full_identifier);
      return std::move(expr);
    }
  }
  else if(!implicit_wire(identifier, symbol))
  {
    // this should become an error
    warning().source_location=expr.source_location();
    warning() << "implicit wire " << symbol->display_name() << eom;
    expr.type()=symbol->type;
    expr.set_identifier(symbol->name);
    return std::move(expr);
  }
  else
  {
    throw errort().with_location(expr.source_location())
      << "unknown identifier " << identifier;
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_hierarchical_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_hierarchical_identifier(
  hierarchical_identifier_exprt expr)
{
  convert_expr(expr.lhs());

  DATA_INVARIANT(expr.rhs().id() == ID_symbol, "expected symbol on rhs of `.'");

  const irep_idt &rhs_identifier = expr.rhs().get_identifier();

  if(expr.lhs().type().id() == ID_struct || expr.lhs().type().id() == ID_union)
  {
    // look up the component
    auto &compound_type = to_struct_union_type(expr.lhs().type());
    auto &component = compound_type.get_component(rhs_identifier);
    if(component.is_nil())
      throw errort().with_location(expr.source_location())
        << compound_type.id() << " does not have a member named "
        << rhs_identifier;

    // create the member expression
    return member_exprt{expr.lhs(), component.get_name(), component.type()}
      .with_source_location(expr);
  }

  const irep_idt &lhs_identifier = [](const exprt &lhs) {
    if(lhs.id() == ID_symbol)
      return to_symbol_expr(lhs).get_identifier();
    else if(lhs.id() == ID_hierarchical_identifier)
      return to_hierarchical_identifier_expr(lhs).identifier();
    else
    {
      throw errort().with_location(lhs.source_location())
        << "expected symbol or hierarchical identifier on lhs of `.'";
    }
  }(expr.lhs());

  if(expr.lhs().type().id() == ID_module_instance)
  {
    // figure out which module the lhs is
    const symbolt *module_instance_symbol;
    if(ns.lookup(lhs_identifier, module_instance_symbol))
    {
      throw errort().with_location(expr.source_location())
        << "failed to find module instance `" << lhs_identifier
        << "' on lhs of `.'";
    }

    const irep_idt &module=module_instance_symbol->value.get(ID_module);

    // the identifier in the module
    const irep_idt full_identifier =
      id2string(module) + "." + id2string(rhs_identifier);

    const symbolt *symbol;
    if(!ns.lookup(full_identifier, symbol))
    {
      if(symbol->type.id() == ID_verilog_genvar)
      {
        throw errort().with_location(expr.source_location())
          << "genvars must not be used in hierarchical identifiers";
      }
      else
      {
        expr.type()=symbol->type;
      }
    }
    else
    {
      throw errort().with_location(expr.source_location())
        << "identifier `" << rhs_identifier << "' not found in module `"
        << module_instance_symbol->pretty_name << "'";
    }

    // We remember the identifier of the symbol.
    expr.identifier(full_identifier);

    return std::move(expr);
  }
  else if(expr.lhs().type().id() == ID_named_block)
  {
    const irep_idt full_identifier =
      id2string(lhs_identifier) + "." + id2string(rhs_identifier);

    const symbolt *symbol;
    if(!ns.lookup(full_identifier, symbol))
    {
      if(symbol->type.id() == ID_verilog_genvar)
      {
        throw errort().with_location(expr.source_location())
          << "genvars must not be used in hierarchical identifiers";
      }
      else
      {
        source_locationt source_location=expr.source_location();

        symbol_exprt symbol_expr=symbol->symbol_expr();
        symbol_expr.add_source_location()=source_location;
        return std::move(symbol_expr);
      }
    }
    else
    {
      throw errort().with_location(expr.source_location())
        << "identifier `" << rhs_identifier << "' not found in named block";
    }
  }
  else  
  {
    throw errort().with_location(expr.source_location())
      << "expected module instance or named block on left-hand side of dot";
  }
  
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_constant(constant_exprt expr)
{
  if(expr.type().id()==ID_string)
  {
    // These are unsigned integer vectors with 8 bits per character.
    // The first character is the most significant one.
    const std::string &value=expr.get_string(ID_value);
    auto type = unsignedbv_typet(value.size() * 8);

    // The below is quadratic, and should be made linear.
    mp_integer new_value = 0;
    for(std::size_t i = 0; i < value.size(); i++)
    {
      unsigned char character = value[i];
      new_value += mp_integer(character) << ((value.size() - i - 1) * 8);
    }

    return from_integer(new_value, type).with_source_location(expr);
  }
  else if(expr.type().id()==ID_unsignedbv ||
          expr.type().id()==ID_signedbv ||
          expr.type().id()==ID_verilog_signedbv ||
          expr.type().id()==ID_verilog_unsignedbv)
  {
    // done already
    return std::move(expr);
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
  bool bits_given=false;

  if(pos!=std::string::npos) // size given?
  {
    if(rest[0]!='\'')
    {
      bits=atoi(rest.c_str());
      bits_given=true;

      if(bits==0)
      {
        throw errort().with_location(expr.source_location())
          << "zero-length bit vector not allowed";
      }
    }

    rest=rest.substr(pos+1);
  }
  
  // signed-flag 's' used?
  bool s_flag_given=false;
  
  if(rest!="" && tolower(rest[0])=='s')
  {
    s_flag_given=true;
    rest=rest.substr(1);
  }

  unsigned base=10;

  // base given?
  bool based=false;

  if(rest!="")
  {
    switch(rest[0])
    {
     case 'b': based=true; base=2;  rest.erase(0, 1); break;
     case 'd': based=true; base=10; rest.erase(0, 1); break;
     case 'h': based=true; base=16; rest.erase(0, 1); break;
     case 'o': based=true; base=8;  rest.erase(0, 1); break;
     default:  base=10;
    }
  }
  
  // based numbers are always unsigned unless 's' flag is given
  bool is_signed=!based || s_flag_given;

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
      throw errort().with_location(expr.source_location())
        << "cannot convert " << value;
    }

    std::string fvalue;

    if(bits_given)
    {
      fvalue=bit_value;

      if(fvalue.size()>bits)
        fvalue.erase(0, fvalue.size()-bits); // cut off...
      else if(fvalue.size()<bits)
      {
        // extend appropriately
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

    if(is_signed)
      expr.type()=verilog_signedbv_typet(bits);
    else
      expr.type()=verilog_unsignedbv_typet(bits);
    
    expr.set(ID_value, fvalue);
    expr.set(ID_C_little_endian, true);
  }
  else
  {
    mp_integer int_value=string2integer(rest, base);
    
    if(!bits_given)
    {
      bits = address_bits(int_value + 1);
      // we do a 32-bit minimum
      if(bits<32) bits=32;
    }

    if(is_signed)
      expr.type()=signedbv_typet(bits);
    else
      expr.type()=unsignedbv_typet(bits);

    expr.set(ID_value, integer2bvrep(int_value, bits));
    expr.set(ID_C_little_endian, true);
  }

  return std::move(expr);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_integer_constant_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer
verilog_typecheck_exprt::convert_integer_constant_expression(exprt expr)
{
  convert_expr(expr);

  // copy the source location, we will modify 'expr'
  auto source_location = expr.source_location();

  // this could be large
  propagate_type(expr, integer_typet());

  exprt tmp = elaborate_constant_expression(expr);

  if(!tmp.is_constant())
  {
    throw errort().with_location(source_location)
      << "expected constant expression, but got `" << to_string(tmp) << '\'';
  }

  const auto &tmp_constant = to_constant_expr(tmp);

  if(tmp_constant.is_true())
    return 1;
  else if(tmp_constant.is_false())
    return 0;
  else
  {
    auto value_opt = numeric_cast<mp_integer>(tmp_constant);
    if(!value_opt.has_value())
    {
      throw errort().with_location(source_location)
        << "failed to convert `" << to_string(tmp_constant)
        << "\' into an integer constant";
    }

    return *value_opt;
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::elaborate_constant_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::elaborate_constant_expression(exprt expr)
{
  // This performs constant-folding on a type-checked expression
  // according to Section 11.2.1 IEEE 1800-2017.

  if(expr.id()==ID_constant)
    return expr;
  else if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_expr(expr).get_identifier();

    if(has_prefix(id2string(identifier), "$"))
    {
      // System function identifier. Leave as is.
      return expr;
    }

    auto &symbol = ns.lookup(to_symbol_expr(expr));

    if(symbol.is_macro)
    {
      // A parameter or local parameter. Replace by its value.
      return symbol.value;
    }

    exprt value=var_value(identifier);
    
    #if 0
    status() << "READ " << identifier << " = " << to_string(value) << eom;
    #endif
      
    if(value.is_not_nil())
    {
      source_locationt source_location=expr.source_location();
      exprt tmp=value;
      tmp.add_source_location()=source_location;
      return tmp;
    }
    else
      return expr;
  }
  else if(expr.id()==ID_function_call)
  {
    // Note that the operands are not elaborated yet.
    const function_call_exprt &function_call=
      to_function_call_expr(expr);

    // Is it a system function call?
    if(function_call.is_system_function_call())
    {
      // These are 'built in'.
      return elaborate_constant_system_function_call(function_call);
    }
    else
    {
      // Use Verilog interpreter.
      return elaborate_constant_function_call(function_call);
    }
  }
  else
  {
    // Remember the Verilog type.
    auto expr_verilog_type = expr.type().get(ID_C_verilog_type);
    auto expr_identifier = expr.type().get(ID_C_identifier);

    // Remember the source location.
    auto location = expr.source_location();

    // Do any operands first.
    bool operands_are_constant = true;

    for(auto &op : expr.operands())
    {
      // recursive call
      op = elaborate_constant_expression(op);
      if(!op.is_constant())
        operands_are_constant = false;
    }

    // Are all operands constants now?
    if(!operands_are_constant)
      return expr; // give up

    if(expr.id() == ID_reduction_or)
    {
      // The simplifier doesn't know how to simplify reduction_or
      auto &reduction_or = to_unary_expr(expr);
      expr = notequal_exprt(
        reduction_or.op(), from_integer(0, reduction_or.op().type()));
    }

    // We fall back to the simplifier to approximate
    // the standard's definition of 'constant expression'.
    auto simplified_expr = simplify_expr(expr, ns);

    // Restore the Verilog type, if any.
    if(expr_verilog_type != irep_idt())
      simplified_expr.type().set(ID_C_verilog_type, expr_verilog_type);

    if(expr_identifier != irep_idt())
      simplified_expr.type().set(ID_C_identifier, expr_identifier);

    if(location.is_not_nil())
      simplified_expr.add_source_location() = location;

    return simplified_expr;
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::elaborate_constant_system_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::elaborate_constant_system_function_call(
  function_call_exprt expr)
{
  // This performs constant-folding on a type-checked function
  // call expression according to Section 11.2.1 IEEE 1800-2017.
  auto &function = expr.function();
  if(function.id() != ID_symbol)
    return std::move(expr); // give up

  auto &identifier = to_symbol_expr(function).get_identifier();

  auto &arguments = expr.arguments();

  if(identifier == "$bits")
  {
    DATA_INVARIANT(arguments.size() == 1, "$bits has one argument");
    return bits(arguments[0]);
  }
  else if(identifier == "$clog2")
  {
    // the ceiling of the log with base 2 of the argument
    DATA_INVARIANT(arguments.size() == 1, "$clog2 has one argument");

    auto op = elaborate_constant_expression(arguments[0]);

    if(!op.is_constant())
      return std::move(expr); // give up

    auto value_opt = numeric_cast<mp_integer>(to_constant_expr(op));
    if(!value_opt.has_value())
      return std::move(expr); // give up

    // SystemVerilog (20.8.1, page 567)
    if(*value_opt == 0 || *value_opt == 1)
      return from_integer(0, integer_typet());
    else
    {
      mp_integer result = 1;
      for(mp_integer x = 2; x < *value_opt; ++result, x *= 2)
        ;

      return from_integer(result, integer_typet());
    }
  }
  else
    return std::move(expr); // don't know it, won't elaborate
}

/*******************************************************************\

Function: verilog_typecheck_exprt::is_constant_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_typecheck_exprt::is_constant_expression(
  const exprt &expr,
  mp_integer &value)
{
  exprt tmp(expr);

  convert_expr(tmp);
  ns.follow_macros(tmp);

  simplify(tmp, ns);

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
  else if(!to_integer_non_constant(tmp, value))
  {
    return true;
  }

  return false;
}

/*******************************************************************\

Function: verilog_typecheck_exprt::implicit_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::implicit_typecast(
  exprt &expr,
  const typet &dest_type)
{
  if(dest_type.id()==irep_idt())
    return;

  const typet &src_type = expr.type();

  auto &verilog_dest_type = dest_type.get(ID_C_verilog_type);
  if(verilog_dest_type == ID_verilog_enum)
  {
    // IEEE 1800-2017 6.19.3: "a variable of type enum cannot be directly
    // assigned a value that lies outside the enumeration set unless an
    // explicit cast is used"
    if(
      src_type.get(ID_C_verilog_type) != ID_verilog_enum ||
      src_type.get(ID_C_identifier) != dest_type.get(ID_C_identifier))
    {
      throw errort().with_location(expr.source_location())
        << "assignment to enum requires enum of the same type, but got "
        << to_string(expr.type());
    }
  }

  if(src_type == dest_type)
    return;

  if(dest_type.id() == ID_integer)
  {
    if(expr.is_constant())
    {
      source_locationt source_location=expr.source_location();
      mp_integer value;

      if(to_integer(to_constant_expr(expr), value))
      {
        throw errort() << "failed to convert integer constant";
      }

      expr = from_integer(value, dest_type);
      expr.add_source_location()=source_location;
      return;
    }

    if(
      src_type.id() == ID_bool || src_type.id() == ID_unsignedbv ||
      src_type.id() == ID_signedbv || src_type.id() == ID_integer)
    {
      expr = typecast_exprt{expr, dest_type};
      return;
    }
  }

  if(src_type.id() == ID_integer)
  {
    // from integer to s.th. else
    if(dest_type.id()==ID_bool)
    {
      // do not use typecast here
      // we actually only want the lowest bit
      unsignedbv_typet tmp_type(1);
      exprt tmp(ID_extractbit, bool_typet());
      exprt no_expr = from_integer(0, integer_typet());
      tmp.add_to_operands(typecast_exprt(expr, tmp_type), std::move(no_expr));
      expr.swap(tmp);
      return;
    }
    else if(dest_type.id()==ID_unsignedbv ||
            dest_type.id()==ID_signedbv ||
            dest_type.id()==ID_verilog_unsignedbv ||
            dest_type.id()==ID_verilog_signedbv)
    {
      expr = typecast_exprt{expr, dest_type};
      return;
    }
  }
  else if(src_type.id() == ID_natural)
  {
    if(dest_type.id()==ID_integer)
    {
      expr = typecast_exprt{expr, dest_type};
      return;
    }
  }
  else if(
    src_type.id() == ID_bool || src_type.id() == ID_unsignedbv ||
    src_type.id() == ID_signedbv || src_type.id() == ID_verilog_unsignedbv ||
    src_type.id() == ID_verilog_signedbv)
  {
    // from bits to s.th. else
    if(dest_type.id()==ID_bool)
    {
      // do not use typecast here
      // we actually only want the lowest bit

      if(expr.is_constant() && src_type.id() == ID_unsignedbv)
      {
        const std::string &value=expr.get_string(ID_value);
        // least significant bit is last
        assert(value.size()!=0);
        expr = make_boolean_expr(value[value.size() - 1] == '1');
        return;
      }

      exprt tmp(ID_extractbit, bool_typet());
      exprt no_expr = from_integer(0, integer_typet());
      tmp.add_to_operands(std::move(expr), std::move(no_expr));
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
        if(to_integer(to_constant_expr(expr), i))
          expr = typecast_exprt{expr, dest_type};
        else
          expr=from_integer(i, dest_type);
      }
      else
        expr = typecast_exprt{expr, dest_type};

      return;
    }
    else if(dest_type.id()==ID_verilog_unsignedbv ||
            dest_type.id()==ID_verilog_signedbv)
    {
      expr = typecast_exprt{expr, dest_type};
      return;
    }
    else if(dest_type.id()==ID_verilog_realtime)
    {
      expr = typecast_exprt{expr, dest_type};
      return;
    }
    else if(dest_type.id() == ID_struct)
    {
      // bit-vectors can be converted to packed structs
      expr = typecast_exprt{expr, dest_type};
      return;
    }
  }
  else if(src_type.id() == ID_struct)
  {
    // packed structs can be converted to bits
    if(
      dest_type.id() == ID_bool || dest_type.id() == ID_unsignedbv ||
      dest_type.id() == ID_signedbv ||
      dest_type.id() == ID_verilog_unsignedbv ||
      dest_type.id() == ID_verilog_signedbv)
    {
      expr = typecast_exprt{expr, dest_type};
      return;
    }
  }

  throw errort().with_location(expr.source_location())
    << "failed to convert `" << to_string(src_type) << "' to `"
    << to_string(dest_type) << "'";
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
    if(!to_integer_non_constant(expr, value))
      expr = make_boolean_expr(value != 0);
    else
      expr = typecast_exprt{expr, bool_typet{}};
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
    throw errort().with_location(range.source_location())
      << "range expected to have two operands";
  }

  msb = convert_integer_constant_expression(to_binary_expr(range).op0());
  lsb = convert_integer_constant_expression(to_binary_expr(range).op1());
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
  // Verilog enum types decay to their base type when used in relational
  // or arithmetic expressions.
  auto enum_decay = [](const typet &type) {
    if(type.get(ID_C_verilog_type) == ID_verilog_enum)
    {
      typet result = type;
      result.remove(ID_C_verilog_type);
      result.remove(ID_C_identifier);
      return result;
    }
    else
      return type;
  };

  const typet new_type =
    max_type(enum_decay(op0.type()), enum_decay(op1.type()));

  if(new_type.is_nil())
  {
    throw errort().with_location(expr.source_location())
      << "expected operands of compatible type but got:\n"
      << "  " << to_string(op0.type()) << '\n'
      << "  " << to_string(op1.type());
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
    
  // If one of the operands is a real, we return the real.
  if(vt0.is_verilog_realtime())
    return t0;
  else if(vt1.is_verilog_realtime())
    return t1;

  bool is_verilogbv=
    vt0.is_verilog_signed() || vt0.is_verilog_unsigned() ||
    vt1.is_verilog_signed() || vt1.is_verilog_unsigned();

  // The result is unsigned if any of the operands is  
  bool is_unsigned=
    vt0.is_unsigned() || vt0.is_bool() || vt0.is_verilog_unsigned() ||
    vt1.is_unsigned() || vt1.is_bool() || vt1.is_verilog_unsigned();
  
  unsigned max_width=std::max(vt0.get_width(), vt1.get_width());

  if(is_verilogbv)
  {
    if(is_unsigned)
      return verilog_unsignedbv_typet(max_width);
    else
      return verilog_signedbv_typet(max_width);
  }
  else
  {
    if(is_unsigned)
      return unsignedbv_typet(max_width);
    else
      return signedbv_typet(max_width);
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
    throw errort().with_location(expr.source_location())
      << "operator " << expr.id_string() << " takes two operands";
  }

  tc_binary_expr(expr, to_binary_expr(expr).op0(), to_binary_expr(expr).op1());
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_unary_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_unary_expr(unary_exprt expr)
{
  if(expr.id()==ID_not)
  {
    // may produce an 'x' if the operand is a verilog_bv
    convert_expr(expr.op());

    if (expr.op().type().id() == ID_verilog_signedbv ||
        expr.op().type().id() == ID_verilog_unsignedbv) {
      expr.type()=verilog_unsignedbv_typet(1);
    }
    else
    {
      expr.type()=bool_typet();
      make_boolean(expr.op());
    }
  }
  else if(expr.id()==ID_reduction_or  || expr.id()==ID_reduction_and ||
          expr.id()==ID_reduction_nor || expr.id()==ID_reduction_nand ||
          expr.id()==ID_reduction_xor || expr.id()==ID_reduction_xnor)
  {
    // these may produce an 'x' if the operand is a verilog_bv
    convert_expr(expr.op());

    if (expr.op().type().id() == ID_verilog_signedbv ||
        expr.op().type().id() == ID_verilog_unsignedbv)
      expr.type()=verilog_unsignedbv_typet(1);
    else
      expr.type()=bool_typet();
  }
  else if(expr.id()==ID_unary_minus ||
          expr.id()==ID_unary_plus)
  {
    convert_expr(expr.op());
    no_bool_ops(expr);
    expr.type() = expr.op().type();
  }
  else if(
    expr.id() == ID_sva_always || expr.id() == ID_sva_nexttime ||
    expr.id() == ID_sva_s_nexttime || expr.id() == ID_sva_s_eventually)
  {
    assert(expr.operands().size()==1);
    convert_expr(expr.op());
    make_boolean(expr.op());
    expr.type()=bool_typet();
  }
  else if(expr.id() == ID_verilog_explicit_cast)
  {
    // SystemVerilog has got type'(expr). This is an explicit
    // type cast.
    convert_expr(expr.op());
    auto new_type = convert_type(expr.type());
    return typecast_exprt{expr.op(), new_type}.with_source_location(expr);
  }
  else if(expr.id() == ID_verilog_implicit_typecast)
  {
    // We generate implict casts during elaboration.
    expr.type() = convert_type(expr.type());
    convert_expr(expr.op());
    expr.id(ID_typecast);
  }
  else
  {
    convert_expr(expr.op());
    expr.type() = expr.op().type();

    // check boolean operators

    if(expr.type().id()==ID_bool && expr.id()==ID_bitnot)
      expr.id(ID_not);
  }

  return std::move(expr);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_bit_select_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_bit_select_expr(binary_exprt expr)
{
  // Verilog's bit select expression may map onto an extractbit
  // or an array index expression, depending on the type of the first
  // operand.
  exprt &op0 = expr.op0();
  convert_expr(op0);

  if(op0.type().id() == ID_verilog_real)
  {
    throw errort().with_location(op0.source_location())
      << "bit-select of real is not allowed";
  }

  if(op0.type().id()==ID_array)
  {
    exprt &op1 = expr.op1();
    convert_expr(op1);
    if(op1.type().id() == ID_verilog_real)
    {
      throw errort().with_location(op1.source_location())
        << "real number index is not allowed";
    }

    typet _index_type = index_type(to_array_type(op0.type()));

    if(_index_type!=op1.type())
    {
      mp_integer i;
      if(!to_integer_non_constant(op1, i))
        op1=from_integer(i, _index_type);
      else if(op1.is_true() || op1.is_false())
        op1=from_integer(op1.is_true()?1:0, _index_type);
      else
        op1 = typecast_exprt{op1, _index_type};
    }

    expr.type() = to_array_type(op0.type()).element_type();
    expr.id(ID_index);
  }
  else
  {
    auto width = get_width(op0.type());
    auto offset = atoi(op0.type().get(ID_C_offset).c_str());

    mp_integer op1;

    if(is_constant_expression(expr.op1(), op1))
    {
      // 1800-2017 sec 11.5.1: out-of-bounds bit-select is
      // x for 4-state and 0 for 2-state values.
      if(op1 < offset || op1 >= width + offset)
        return false_exprt().with_source_location(expr);

      op1 -= offset;
      expr.op1() = from_integer(op1, natural_typet());
    }
    else
    {
      convert_expr(expr.op1());
      if(expr.op1().type().id() == ID_verilog_real)
      {
        throw errort().with_location(expr.op1().source_location())
          << "real number index is not allowed";
      }
    }

    expr.type()=bool_typet();
    expr.id(ID_extractbit);
  }

  return std::move(expr);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_replication_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_replication_expr(replication_exprt expr)
{
  exprt &op1=expr.op1();

  convert_expr(op1);

  if(op1.type().id()==ID_array)
  {
    throw errort().with_location(op1.source_location())
      << "array type not allowed in replication";
  }

  if(op1.type().id()==ID_bool)
    op1 = typecast_exprt{op1, unsignedbv_typet{1}};

  auto width = get_width(expr.op1().type());

  mp_integer op0 = convert_integer_constant_expression(expr.op0());

  if(op0<0)
  {
    throw errort().with_location(expr.source_location())
      << "number of replications must not be negative";
  }

  // IEEE 1800-2017 explicitly allows replication with
  // count zero.

  {
    expr.op0()=from_integer(op0, natural_typet());

    auto new_width = op0 * width;
    auto new_width_int = numeric_cast_v<std::size_t>(new_width);

    if(op1.type().id()==ID_verilog_unsignedbv ||
       op1.type().id()==ID_verilog_signedbv)
      expr.type() = verilog_unsignedbv_typet{new_width_int};
    else
      expr.type() = unsignedbv_typet{new_width_int};
  }

  return std::move(expr);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_shl_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_shl_expr(shl_exprt expr)
{
  convert_expr(expr.op0());
  convert_expr(expr.op1());
  
  no_bool_ops(expr);

  // the bit width of a shift is always the bit width of the left operand
  const typet &op0_type=expr.op0().type();
  
  expr.type()=op0_type;

  return std::move(expr);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_binary_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_binary_expr(binary_exprt expr)
{
  if(expr.id() == ID_verilog_bit_select)
    return convert_bit_select_expr(to_binary_expr(expr));
  else if(expr.id()==ID_replication)
    return convert_replication_expr(to_replication_expr(expr));
  else if(
    expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_iff ||
    expr.id() == ID_implies)
  {
    Forall_operands(it, expr)
    {
      convert_expr(*it);
      make_boolean(*it);
    }

    expr.type()=bool_typet();

    return std::move(expr);
  }
  else if(expr.id()==ID_equal || expr.id()==ID_notequal)
  {
    expr.type()=bool_typet();

    Forall_operands(it, expr)
      convert_expr(*it);

    tc_binary_expr(expr);

    return std::move(expr);
  }
  else if(expr.id()==ID_verilog_case_equality ||
          expr.id()==ID_verilog_case_inequality)
  {
    expr.type()=bool_typet();

    Forall_operands(it, expr)
      convert_expr(*it);

    tc_binary_expr(expr);

    return std::move(expr);
  }
  else if(expr.id()==ID_lt || expr.id()==ID_gt ||
          expr.id()==ID_le || expr.id()==ID_ge)
  {
    expr.type()=bool_typet();

    Forall_operands(it, expr)
      convert_expr(*it);

    tc_binary_expr(expr);
    no_bool_ops(expr);

    return std::move(expr);
  }
  else if(expr.id()==ID_shl)
    return convert_shl_expr(to_shl_expr(expr));
  else if(expr.id()==ID_shr)
  {
    // This is the >>> expression, which turns into ID_lshr or ID_ashr
    // depending on type of first operand.

    convert_expr(expr.op0());
    convert_expr(expr.op1());
    no_bool_ops(expr);

    const typet &op0_type = expr.op0().type();

    if(
      op0_type.id() == ID_signedbv || op0_type.id() == ID_verilog_signedbv ||
      op0_type.id() == ID_integer)
      expr.id(ID_ashr);
    else
      expr.id(ID_lshr);

    expr.type()=op0_type;

    return std::move(expr);
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
    no_bool_ops(expr);
    expr.type()=expr.op0().type();

    return std::move(expr);
  }
  else if(expr.id()==ID_div || expr.id()==ID_mod)
  {
    Forall_operands(it, expr)
      convert_expr(*it);

    tc_binary_expr(expr);
    no_bool_ops(expr);

    expr.type()=expr.op0().type();

    return std::move(expr);
  }
  else if(expr.id()==ID_sva_overlapped_implication ||
          expr.id()==ID_sva_non_overlapped_implication ||
          expr.id()==ID_sva_until ||
          expr.id()==ID_sva_s_until ||
          expr.id()==ID_sva_until_with ||
          expr.id()==ID_sva_s_until_with)
  {
    convert_expr(expr.op0());
    make_boolean(expr.op0());
    convert_expr(expr.op1());
    make_boolean(expr.op1());
    expr.type()=bool_typet();

    return std::move(expr);
  }
  else if(expr.id()==ID_hierarchical_identifier)
  {
    return convert_hierarchical_identifier(
      to_hierarchical_identifier_expr(std::move(expr)));
  }
  else if(expr.id() == ID_verilog_size_cast)
  {
    // SystemVerilog has got expr'(expr). This is an explicit
    // type cast, to change the size (in bits) of the rhs to the
    // number given as lhs.
    convert_expr(expr.rhs());
    auto new_size = convert_integer_constant_expression(expr.lhs());
    auto new_size_int = numeric_cast_v<std::size_t>(new_size);
    auto &op_type = expr.rhs().type();
    if(op_type.id() == ID_signedbv)
    {
      return typecast_exprt{expr.rhs(), signedbv_typet{new_size_int}}
        .with_source_location(expr);
    }
    else if(op_type.id() == ID_unsignedbv)
    {
      return typecast_exprt{expr.rhs(), unsignedbv_typet{new_size_int}}
        .with_source_location(expr);
    }
    else
    {
      throw errort().with_location(expr.source_location())
        << "cannot perform size cast on " << to_string(op_type);
    }
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
       expr.id()==ID_mult ||
       expr.id()==ID_power)
      no_bool_ops(expr);

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

    return std::move(expr);
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_trinary_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_trinary_expr(ternary_exprt expr)
{
  if(expr.id() == ID_verilog_non_indexed_part_select)
  {
    auto &part_select = to_verilog_non_indexed_part_select_expr(expr);
    exprt &src = part_select.src();
    convert_expr(src);

    if(src.type().id() == ID_array)
    {
      throw errort().with_location(src.source_location())
        << "array type not allowed in part select";
    }

    if(src.type().id() == ID_verilog_real)
    {
      throw errort().with_location(src.source_location())
        << "real not allowed in part select";
    }

    mp_integer src_width = get_width(src.type());
    mp_integer src_offset = string2integer(src.type().get_string(ID_C_offset));

    // In non-indexed part-select expressions, both
    // indices must be constants (1800-2017 11.5.1).
    mp_integer msb = convert_integer_constant_expression(part_select.msb());
    mp_integer lsb = convert_integer_constant_expression(part_select.lsb());

    if(msb < lsb)
      std::swap(msb, lsb); // now msb>=lsb

    // 1800-2017 sec 11.5.1: out-of-bounds bit-select is
    // x for 4-state and 0 for 2-state values. We
    // achieve that by padding the operand from either end,
    // or both.
    if(lsb < src_offset)
    {
      auto padding_width = src_offset - lsb;
      auto padding = from_integer(
        0, unsignedbv_typet{numeric_cast_v<std::size_t>(padding_width)});
      auto new_type = unsignedbv_typet{
        numeric_cast_v<std::size_t>(get_width(src.type()) + padding_width)};
      src = concatenation_exprt(src, padding, new_type);
      lsb += padding_width;
      msb += padding_width;
    }

    if(msb >= src_width + src_offset)
    {
      auto padding_width = msb - (src_width + src_offset) + 1;
      auto padding = from_integer(
        0, unsignedbv_typet{numeric_cast_v<std::size_t>(padding_width)});
      auto new_type = unsignedbv_typet{
        numeric_cast_v<std::size_t>(get_width(src.type()) + padding_width)};
      src = concatenation_exprt(padding, src, new_type);
    }

    // Part-select expressions are unsigned, even if the
    // entire expression is selected!
    auto expr_type =
      unsignedbv_typet{numeric_cast_v<std::size_t>(msb - lsb + 1)};

    lsb -= src_offset;
    msb -= src_offset;

    // Construct the extractbits expression
    expr.id(ID_extractbits);
    expr.op1() = from_integer(msb, integer_typet());
    expr.op2() = from_integer(lsb, integer_typet());
    expr.type() = expr_type;

    return std::move(expr);
  }
  else if(
    expr.id() == ID_verilog_indexed_part_select_plus ||
    expr.id() == ID_verilog_indexed_part_select_minus)
  {
    auto &part_select = to_verilog_indexed_part_select_plus_or_minus_expr(expr);
    exprt &src = part_select.src();
    convert_expr(src);

    if(src.type().id() == ID_array)
    {
      throw errort().with_location(src.source_location())
        << "array type not allowed in part select";
    }

    if(src.type().id() == ID_verilog_real)
    {
      throw errort().with_location(src.source_location())
        << "real not allowed in part select";
    }

    mp_integer src_width = get_width(src.type());
    mp_integer src_offset = string2integer(src.type().get_string(ID_C_offset));

    // The index need not be a constant.
    exprt &index = part_select.index();
    convert_expr(index);

    // The width of the indexed part select must be an
    // elaboration-time constant.
    mp_integer width = convert_integer_constant_expression(part_select.width());

    // The width must be positive. 1800-2017 11.5.1
    if(width < 0)
    {
      throw errort().with_location(part_select.width().source_location())
        << "width of indexed part select must be positive";
    }

    // Part-select expressions are unsigned, even if the
    // entire expression is selected!
    auto expr_type = unsignedbv_typet{numeric_cast_v<std::size_t>(width)};

    mp_integer index_int;
    if(is_constant_expression(index, index_int))
    {
      // Construct the extractbits expression
      mp_integer bottom, top;

      if(part_select.id() == ID_verilog_indexed_part_select_plus)
      {
        bottom = index_int - src_offset;
        top = bottom + width;
      }
      else // ID_verilog_indexed_part_select_minus
      {
        top = index_int - src_offset;
        bottom = bottom - width;
      }

      return extractbits_exprt{
        std::move(src),
        from_integer(top, integer_typet{}),
        from_integer(bottom, integer_typet{}),
        std::move(expr_type)}
        .with_source_location(expr);
    }
    else
    {
      // Index not constant.
      // Use logical right-shift followed by (constant) extractbits.
      auto index_adjusted =
        minus_exprt{index, from_integer(src_offset, index.type())};

      auto src_shifted = lshr_exprt(src, index_adjusted);

      return extractbits_exprt{
        std::move(src_shifted),
        from_integer(width - 1, integer_typet{}),
        from_integer(0, integer_typet{}),
        std::move(expr_type)}
        .with_source_location(expr);
    }
  }
  else if(expr.id()==ID_if)
  {
    convert_expr(expr.op0());
    make_boolean(expr.op0());
    convert_expr(expr.op1());
    convert_expr(expr.op2());

    tc_binary_expr(expr, expr.op1(), expr.op2());
    expr.type()=expr.op1().type();
    return std::move(expr);
  }
  else if(expr.id()==ID_sva_cycle_delay) // #[1:2] something
  {
    expr.type()=bool_typet();
    assert(expr.operands().size()==3);
    convert_expr(expr.op0());
    if(expr.op1().is_not_nil()) convert_expr(expr.op1());
    convert_expr(expr.op2());
    make_boolean(expr.op2());
    return std::move(expr);
  }
  else if(
    expr.id() == ID_sva_eventually || expr.id() == ID_sva_ranged_always ||
    expr.id() == ID_sva_s_always)
  {
    auto lower = convert_integer_constant_expression(expr.op0());

    expr.op0() =
      from_integer(lower, natural_typet()).with_source_location(expr.op0());

    if(expr.op1().id() == ID_infinity)
    {
    }
    else
    {
      auto upper = convert_integer_constant_expression(expr.op1());
      if(lower > upper)
      {
        throw errort().with_location(expr.source_location())
          << "range must be lower <= upper";
      }

      expr.op1() =
        from_integer(upper, natural_typet()).with_source_location(expr.op1());
    }

    convert_expr(expr.op2());
    make_boolean(expr.op2());
    expr.type() = bool_typet();

    return std::move(expr);
  }
  else
  {
    throw errort().with_location(expr.source_location())
      << "no conversion for trinary expression " << expr.id();
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
  const unsigned errors_before=
    message_handler.get_message_count(messaget::M_ERROR);

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
    verilog_typecheck_expr.error() << e << messaget::eom;
  }

  catch(const std::string &e)
  {
    verilog_typecheck_expr.error() << e << messaget::eom;
  }

  catch(const verilog_typecheck_baset::errort &e)
  {
    if(e.what().empty())
      verilog_typecheck_expr.error();
    else
    {
      verilog_typecheck_expr.error().source_location = e.source_location();
      verilog_typecheck_expr.error() << e.what() << messaget::eom;
    }
  }

  return message_handler.get_message_count(messaget::M_ERROR)!=errors_before;
}
