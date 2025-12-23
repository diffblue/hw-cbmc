/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_typecheck_expr.h"

#include <util/bitvector_expr.h>
#include <util/ebmc_util.h>
#include <util/expr_util.h>
#include <util/ieee_float.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/string2int.h>

#include "aval_bval_encoding.h"
#include "convert_literals.h"
#include "expr2verilog.h"
#include "typename.h"
#include "verilog_bits.h"
#include "verilog_expr.h"
#include "verilog_lowering.h"
#include "verilog_simplifier.h"
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

Function: verilog_typecheck_exprt::assignment_conversion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::assignment_conversion(
  exprt &rhs,
  const typet &lhs_type)
{
  // 1800-2017 10.9
  if(rhs.type().id() == ID_verilog_assignment_pattern)
  {
    DATA_INVARIANT(
      rhs.id() == ID_verilog_assignment_pattern,
      "verilog_assignment_pattern expression expected");

    if(lhs_type.id() == ID_struct)
    {
      auto &struct_type = to_struct_type(lhs_type);
      auto &components = struct_type.components();

      if(
        !rhs.operands().empty() &&
        rhs.operands().front().id() == ID_member_initializer)
      {
        exprt::operandst initializers{components.size(), nil_exprt{}};

        for(auto &op : rhs.operands())
        {
          PRECONDITION(op.id() == ID_member_initializer);
          auto member_name = op.get(ID_member_name);
          if(!struct_type.has_component(member_name))
          {
            throw errort().with_location(op.source_location())
              << "struct does not have a member `" << member_name << "'";
          }
          auto nr = struct_type.component_number(member_name);
          auto value = to_unary_expr(op).op();
          // rec. call
          assignment_conversion(value, components[nr].type());
          initializers[nr] = std::move(value);
        }

        // Is every member covered?
        for(std::size_t i = 0; i < components.size(); i++)
          if(initializers[i].is_nil())
          {
            throw errort().with_location(rhs.source_location())
              << "assignment pattern does not assign member `"
              << components[i].get_name() << "'";
          }

        rhs = struct_exprt{std::move(initializers), struct_type}
                .with_source_location(rhs.source_location());
      }
      else
      {
        if(rhs.operands().size() != components.size())
        {
          throw errort().with_location(rhs.source_location())
            << "number of expressions does not match number of struct members";
        }

        for(std::size_t i = 0; i < components.size(); i++)
        {
          // rec. call
          assignment_conversion(rhs.operands()[i], components[i].type());
        }

        // turn into struct expression
        rhs.id(ID_struct);
        rhs.type() = lhs_type;
      }

      return;
    }
    else if(lhs_type.id() == ID_array)
    {
      auto &array_type = to_array_type(lhs_type);
      auto &element_type = array_type.element_type();
      auto array_size =
        numeric_cast_v<mp_integer>(to_constant_expr(array_type.size()));

      if(array_size != rhs.operands().size())
      {
        throw errort().with_location(rhs.source_location())
          << "number of expressions does not match number of array elements";
      }

      for(std::size_t i = 0; i < array_size; i++)
      {
        // rec. call
        assignment_conversion(rhs.operands()[i], element_type);
      }

      // turn into array expression
      rhs.id(ID_array);
      rhs.type() = lhs_type;
      return;
    }
    else
    {
      throw errort().with_location(rhs.source_location())
        << "cannot convert assignment pattern to '" << to_string(lhs_type)
        << '\'';
    }
  }

  auto original_rhs_type = rhs.type(); // copy

  auto &verilog_dest_type = lhs_type.get(ID_C_verilog_type);
  if(verilog_dest_type == ID_verilog_enum)
  {
    // IEEE 1800-2017 6.19.3: "a variable of type enum cannot be directly
    // assigned a value that lies outside the enumeration set unless an
    // explicit cast is used"
    if(
      rhs.type().get(ID_C_verilog_type) != ID_verilog_enum ||
      rhs.type().get(ID_C_identifier) != lhs_type.get(ID_C_identifier))
    {
      throw errort().with_location(rhs.source_location())
        << "assignment to enum requires enum of the same type, but got "
        << to_string(rhs.type());
    }
  }

  if(lhs_type == rhs.type())
    return;

  if(lhs_type.id() == ID_struct && !lhs_type.get_bool(ID_packed))
  {
    // assignment of a non-matching type to unpacked struct
    throw errort().with_location(rhs.source_location())
      << "failed to convert `" << to_string(original_rhs_type) << "' to `"
      << to_string(lhs_type) << "'";
  }

  // do enum, union and struct decay
  enum_decay(rhs);
  struct_decay(rhs);
  union_decay(rhs);

  if(rhs.type().id() == ID_struct || rhs.type().id() == ID_union)
  {
    // not decayed, not equal
    throw errort().with_location(rhs.source_location())
      << "failed to convert `" << to_string(original_rhs_type) << "' to `"
      << to_string(lhs_type) << "'";
  }

  // Implements 1800-2017 10.7 and 1800-2017 11.8.3.

  if(
    lhs_type.id() == ID_verilog_real || lhs_type.id() == ID_verilog_shortreal ||
    lhs_type.id() == ID_verilog_realtime ||
    rhs.type().id() == ID_verilog_real ||
    rhs.type().id() == ID_verilog_shortreal)
  {
    // from/to real is just a cast
    rhs = typecast_exprt::conditional_cast(rhs, lhs_type);
    return;
  }

  if(rhs.type().id() == ID_verilog_null)
  {
    if(
      lhs_type.id() == ID_verilog_chandle ||
      lhs_type.id() == ID_verilog_class_type ||
      lhs_type.id() == ID_verilog_event)
    {
      rhs = typecast_exprt{rhs, lhs_type};
      return;
    }
  }

  if(rhs.type().id() == ID_verilog_new)
  {
    if(lhs_type.id() == ID_verilog_class_type)
    {
      rhs = typecast_exprt{rhs, lhs_type};
      return;
    }
  }

  // "The size of the left-hand side of an assignment forms
  // the context for the right-hand expression."

  // Get the width of LHS and RHS
  auto lhs_width = get_width(lhs_type);
  auto rhs_width = get_width(rhs.type());

  if(lhs_width > rhs_width)
  {
    // Need to enlarge the RHS.
    //
    // "If needed, extend the size of the right-hand side,
    // performing sign extension if, and only if, the type
    // of the right-hand side is signed.
    if(
      (rhs.type().id() == ID_signedbv ||
       rhs.type().id() == ID_verilog_signedbv) &&
      (lhs_type.id() == ID_unsignedbv ||
       lhs_type.id() == ID_verilog_unsignedbv))
    {
      // LHS is unsigned, RHS is signed. Must sign-extend.
      auto new_rhs_type = to_bitvector_type(rhs.type());
      new_rhs_type.set_width(numeric_cast_v<std::size_t>(lhs_width));

      downwards_type_propagation(rhs, new_rhs_type);

      // then cast
      rhs = typecast_exprt::conditional_cast(rhs, lhs_type);
    }
    else
      downwards_type_propagation(rhs, lhs_type);
  }
  else if(lhs_width == rhs_width)
  {
    // size stays the same -- this is a reinterpret cast
    rhs = typecast_exprt::conditional_cast(rhs, lhs_type);
  }
  else // lhs_width < rhs_width
  {
    // we shrink -- this is truncation
    if(lhs_type.id() == ID_bool)
      rhs = extractbit_exprt{rhs, from_integer(0, integer_typet{})};
    else
      rhs = typecast_exprt{rhs, lhs_type};
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::downwards_type_progatation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::downwards_type_propagation(
  exprt &expr,
  const typet &type)
{
  // This implements the step "propagate the type and size down to
  // the context-determined operands" in 1800-2017 11.8.2

  // Any context-determined operand of an operator shall be the
  // same type and size as the result of the operator.
  // As an exception, if the result type is real, the operands
  // are just casted.

  if(expr.type() == type)
    return;

  if(type.id() == ID_verilog_real || type.id() == ID_verilog_shortreal)
  {
    expr = typecast_exprt{expr, type};
    return;
  }

  // expressions with context-determined width, following
  // 1800-2017 Table 11-21
  if(
    expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult ||
    expr.id() == ID_div || expr.id() == ID_mod || expr.id() == ID_bitand ||
    expr.id() == ID_bitor || expr.id() == ID_bitxor ||
    expr.id() == ID_bitxnor || expr.id() == ID_unary_plus ||
    expr.id() == ID_unary_minus || expr.id() == ID_bitnot)
  {
    // All operands are context-determined.
    for(auto &op : expr.operands())
      downwards_type_propagation(op, type);
    expr.type() = type;
    return;
  }
  else if(
    expr.id() == ID_shl || expr.id() == ID_ashr || expr.id() == ID_lshr ||
    expr.id() == ID_power)
  {
    // The LHS is context-determined, the RHS is self-determined
    auto &binary_expr = to_binary_expr(expr);
    downwards_type_propagation(binary_expr.lhs(), type);
    expr.type() = type;
    return;
  }
  else if(expr.id() == ID_if)
  {
    // The first operand is self-determined, the others are context-determined
    auto &if_expr = to_if_expr(expr);
    downwards_type_propagation(if_expr.op1(), type);
    downwards_type_propagation(if_expr.op2(), type);
    expr.type() = type;
    return;
  }

  // Just cast the expression, leave any operands as they are.
  if(
    (expr.type().id() == ID_signedbv ||
     expr.type().id() == ID_verilog_signedbv) &&
    (type.id() == ID_unsignedbv || type.id() == ID_verilog_unsignedbv) &&
    get_width(expr.type()) < get_width(type))
  {
    // "If the operand shall be extended, then it shall be sign-extended only
    // if the propagated type is signed."
    // A typecast from signed to a larger unsigned would sign extend.
    expr = zero_extend_exprt{expr, type};
  }
  else
  {
    expr = typecast_exprt{expr, type};
  }
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

Function: verilog_typecheck_exprt::must_be_bit_vector

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::must_be_bit_vector(exprt &expr)
{
  // Throw an error if the given expression doesn't have a bitvector type.
  const auto &type = expr.type();
  if(type.id() == ID_bool)
  {
    // ok as is
  }
  else if(
    type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
    type.id() == ID_verilog_unsignedbv || type.id() == ID_verilog_signedbv)
  {
    // ok as is
  }
  else
    throw errort().with_location(expr.source_location())
      << "operand " << to_string(expr) << " must have a bit vector type";
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_expr_concatenation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_expr_concatenation(
  concatenation_exprt expr)
{
  if(expr.operands().size() == 0)
  {
    throw errort().with_location(expr.source_location())
      << "concatenation expected to have at least one operand";
  }

  mp_integer width = 0;
  bool has_verilogbv = false;

  Forall_operands(it, expr)
  {
    convert_expr(*it);

    // check if there's an unsized literal (1800-2017 11.4.12)
    if(it->get_bool(ID_C_verilog_unsized))
    {
      throw errort().with_location(it->source_location())
        << "unsized literals are not allowed in concatenations";
    }

    must_be_bit_vector(*it);

    const typet &type = it->type();

    if(type.id() == ID_verilog_signedbv || type.id() == ID_verilog_unsignedbv)
    {
      has_verilogbv = true;
    }

    width += get_width(*it);
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

  expr.type() = typet(has_verilogbv ? ID_verilog_unsignedbv : ID_unsignedbv);
  expr.type().set(ID_width, integer2string(width));

  if(has_verilogbv)
  {
    Forall_operands(it, expr)
      if(it->type().id() != ID_verilog_unsignedbv)
      {
        auto width_int = numeric_cast_v<std::size_t>(get_width(*it));
        *it = typecast_exprt{*it, verilog_unsignedbv_typet{width_int}};
      }
  }

  return std::move(expr);
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

  if(expr.id() == ID_verilog_event)
  {
    expr.type() = bool_typet();

    Forall_operands(it, expr)
      convert_expr(*it);

    return expr;
  }
  else if(expr.id() == ID_concatenation)
  {
    return convert_expr_concatenation(to_concatenation_expr(expr));
  }
  else if(expr.id()==ID_function_call)
  {
    return convert_expr_function_call(to_function_call_expr(expr));
  }
  else if(expr.id() == ID_verilog_assignment_pattern)
  {
    // multi-ary -- may become a struct or array, depending
    // on context.
    for(auto &op : expr.operands())
      convert_expr(op);

    // Typechecking can only be completed once we know the type
    // from the usage context. We record "verilog_assignment_pattern"
    // to signal that.
    expr.type() = typet(ID_verilog_assignment_pattern);

    return expr;
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

  // built-in functions
  if(expr.is_system_function_call())
    return convert_system_function(expr);

  if(expr.function().id() != ID_verilog_identifier)
  {
    throw errort().with_location(expr.source_location())
      << "expected identifier as function";
  }

  exprt &f_op = expr.function();

  const irep_idt &base_name = to_verilog_identifier_expr(f_op).base_name();

  std::string full_identifier =
    id2string(module_identifier) + "." + id2string(base_name);

  const symbolt *symbol;
  if(ns.lookup(full_identifier, symbol))
  {
    throw errort().with_location(f_op.source_location())
      << "unknown function `" << base_name << "'";
  }

  if(symbol->type.id()!=ID_code)
  {
    throw errort().with_location(f_op.source_location())
      << "expected function name";
  }

  const code_typet &code_type=to_code_type(symbol->type);

  f_op = symbol->symbol_expr().with_source_location(f_op);
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
    assignment_conversion(arguments[i], parameter_types[i].type());

  return std::move(expr);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::isunknown

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt verilog_typecheck_exprt::isunknown(const constant_exprt &expr)
{
  // constant folding for $isunknown
  auto bval = ::bval(expr);
  auto bval_simplified = verilog_simplifier(bval, ns);
  CHECK_RETURN(bval_simplified.is_constant());
  auto all_zeros = to_bv_type(bval_simplified.type()).all_zeros_expr();
  if(bval_simplified == all_zeros)
    return false_exprt{};
  else
    return true_exprt{};
}

/*******************************************************************\

Function: verilog_typecheck_exprt::bits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::bits(const exprt &expr)
{
  auto bits_opt = verilog_bits_opt(expr.type());

  if(!bits_opt.has_value())
  {
    throw errort().with_location(expr.source_location())
      << "failed to determine number of bits of " << to_string(expr);
  }

  return from_integer(bits_opt.value(), integer_typet())
    .with_source_location(expr.source_location());
}

/*******************************************************************\

Function: verilog_typecheck_exprt::left

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt verilog_typecheck_exprt::left(const exprt &expr)
{
  return from_integer(verilog_left(expr.type()), integer_typet{});
}

/*******************************************************************\

Function: verilog_typecheck_exprt::right

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt verilog_typecheck_exprt::right(const exprt &expr)
{
  return from_integer(verilog_right(expr.type()), integer_typet{});
}

/*******************************************************************\

Function: verilog_typecheck_exprt::countones

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt verilog_typecheck_exprt::countones(const constant_exprt &expr)
{
  // lower to popcount and try simplifier
  auto simplified =
    simplify_expr(popcount_exprt{expr, verilog_int_typet{}.lower()}, ns);

  if(!simplified.is_constant())
  {
    throw errort{}.with_location(expr.source_location())
      << "failed to simplify constant $countones";
  }
  else
    return to_constant_expr(simplified);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::increment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt verilog_typecheck_exprt::increment(const exprt &expr)
{
  // fixed-size dimension: 1 if $left >= $right, -1 otherwise
  auto increment = [](const typet &type) -> mp_integer {
    if(
      type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
      type.id() == ID_verilog_unsignedbv || type.id() == ID_verilog_signedbv ||
      type.id() == ID_array)
    {
      if(type.get_bool(ID_C_increasing))
        return -1;
      else
        return 1;
    }
    else
      return -1;
  };

  return from_integer(increment(expr.type()), integer_typet{});
}

/*******************************************************************\

Function: verilog_typecheck_exprt::low

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt verilog_typecheck_exprt::low(const exprt &expr)
{
  // $left if $increment returns –1
  // $right otherwise
  if(numeric_cast_v<mp_integer>(increment(expr)) == -1)
    return left(expr);
  else
    return right(expr);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::high

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt verilog_typecheck_exprt::high(const exprt &expr)
{
  // $right if $increment returns –1
  // $left otherwise
  if(numeric_cast_v<mp_integer>(increment(expr)) == -1)
    return right(expr);
  else
    return left(expr);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::typename_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::typename_string(const exprt &expr)
{
  auto s = verilog_typename(expr.type());
  return convert_string_literal(s).with_source_location(expr);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_system_function

  Inputs:

 Outputs:

 Purpose: Takes care of functions that start with $

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_system_function(function_call_exprt expr)
{
  auto base_name = to_verilog_identifier_expr(expr.function()).base_name();

  exprt::operandst &arguments=expr.arguments();

  if(base_name == "$signed")
  {
    // this is an explicit type cast
    if(arguments.size()!=1)
    {
      throw errort().with_location(expr.source_location())
        << "$signed takes one argument";
    }
    
    exprt &argument=arguments.front();
    
    if(argument.type().id()==ID_signedbv)
    {
      expr.type() = argument.type();
      return std::move(expr);
    }
    else if(argument.type().id()==ID_unsignedbv)
    {
      typet new_type = argument.type();
      new_type.id(ID_signedbv);
      expr.type() = new_type;
      return std::move(expr);
    }
    else if(argument.type().id()==ID_bool)
    {
      expr.type() = signedbv_typet{1};
      return std::move(expr);
    }
    else
    {
      throw errort().with_location(expr.source_location())
        << "$signed takes an unsigned bit-vector as argument, but got `"
        << to_string(argument.type()) << '\'';
    }
  }
  else if(base_name == "$unsigned")
  {
    // this is an explicit type cast
    if(arguments.size()!=1)
    {
      throw errort().with_location(expr.source_location())
        << "$unsigned takes one argument";
    }
    
    exprt &argument=arguments.front();

    if(argument.type().id()==ID_unsignedbv)
    {
      expr.type() = argument.type();
      return std::move(expr);
    }
    else if(argument.type().id()==ID_signedbv)
    {
      typet new_type = argument.type();
      new_type.id(ID_unsignedbv);
      expr.type() = new_type;
      return std::move(expr);
    }
    else if(argument.type().id()==ID_bool)
    {
      expr.type() = unsignedbv_typet{1};
      return std::move(expr);
    }
    else
    {
      throw errort().with_location(expr.source_location())
        << "$unsigned takes an unsigned bit-vector as argument, but got `"
        << to_string(argument.type()) << '\'';
    }
  }
  else if(base_name == "$ND")
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
  else if(
    base_name == "$bits" || base_name == "$left" || base_name == "$right" ||
    base_name == "$increment" || base_name == "$low" || base_name == "$high")
  {
    if(arguments.size() != 1)
    {
      throw errort().with_location(expr.source_location())
        << base_name << " takes one argument";
    }

    // The return type is integer.
    expr.type() = integer_typet();

    return std::move(expr);
  }
  else if(base_name == "$countones") // SystemVerilog
  {
    if(arguments.size() != 1)
    {
      throw errort().with_location(expr.source_location())
        << "$countones takes one argument";
    }

    // The return type is 'int'
    expr.type() = verilog_int_typet{}.lower();

    return std::move(expr);
  }
  else if(base_name == "$onehot") // SystemVerilog
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
  else if(base_name == "$onehot0") // SystemVerilog
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
  else if(base_name == "$clog2") // Verilog-2005
  {
    if(arguments.size() != 1)
    {
      throw errort().with_location(expr.source_location())
        << "$clog2 takes one argument";
    }

    expr.type() = integer_typet();

    return std::move(expr);
  }
  else if(base_name == "$isunknown")
  {
    if(arguments.size() != 1)
    {
      throw errort().with_location(expr.source_location())
        << "$isunknown takes one argument";
    }

    expr.type() = bool_typet();

    return std::move(expr);
  }
  else if(base_name == "$past")
  {
    if(arguments.size() == 0 || arguments.size() >= 4)
    {
      throw errort().with_location(expr.source_location())
        << "$past takes one to four arguments";
    }

    if(arguments.size() >= 2)
    {
      auto tmp = elaborate_constant_expression_check(arguments[1]);
      arguments[1] = tmp;
    }

    expr.type() = arguments.front().type();

    return std::move(expr);
  }
  else if(
    base_name == "$stable" || base_name == "$rose" || base_name == "$fell" ||
    base_name == "$changed")
  {
    if(arguments.size() != 1 && arguments.size() != 2)
    {
      throw errort().with_location(expr.source_location())
        << base_name << " takes one or two arguments";
    }

    expr.type() = bool_typet();

    return std::move(expr);
  }
  else if(base_name == "$rtoi")
  {
    if(arguments.size() != 1)
    {
      throw errort().with_location(expr.source_location())
        << base_name << " takes one argument";
    }

    expr.type() = verilog_integer_typet();

    return std::move(expr);
  }
  else if(base_name == "$itor")
  {
    if(arguments.size() != 1)
    {
      throw errort().with_location(expr.source_location())
        << base_name << " takes one argument";
    }

    expr.type() = verilog_real_typet();

    return std::move(expr);
  }
  else if(base_name == "$bitstoreal")
  {
    if(arguments.size() != 1)
    {
      throw errort().with_location(expr.source_location())
        << base_name << " takes one argument";
    }

    expr.type() = verilog_real_typet();

    return std::move(expr);
  }
  else if(base_name == "$bitstoshortreal")
  {
    if(arguments.size() != 1)
    {
      throw errort().with_location(expr.source_location())
        << base_name << " takes one argument";
    }

    expr.type() = verilog_shortreal_typet();

    return std::move(expr);
  }
  else if(base_name == "$realtobits")
  {
    if(arguments.size() != 1)
    {
      throw errort().with_location(expr.source_location())
        << base_name << " takes one argument";
    }

    arguments[0] =
      typecast_exprt::conditional_cast(arguments[0], verilog_real_typet{});

    expr.type() = unsignedbv_typet{64};

    return std::move(expr);
  }
  else if(base_name == "$shortrealtobits")
  {
    if(arguments.size() != 1)
    {
      throw errort().with_location(expr.source_location())
        << base_name << " takes one argument";
    }

    arguments[0] =
      typecast_exprt::conditional_cast(arguments[0], verilog_shortreal_typet{});

    expr.type() = unsignedbv_typet{32};

    return std::move(expr);
  }
  else if(base_name == "$typename")
  {
    if(arguments.size() != 1)
    {
      throw errort().with_location(expr.source_location())
        << "$typename takes one argument";
    }

    // just get the function return type for now
    auto value = typename_string(arguments[0]);

    expr.type() = value.type();

    return std::move(expr);
  }
  else
  {
    throw errort().with_location(expr.function().source_location())
      << "unknown system function `" << base_name << "'";
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
  else if(expr.id() == ID_verilog_identifier)
  {
    return convert_verilog_identifier(
      to_verilog_identifier_expr(std::move(expr)), {});
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
    expr.type() = elaborate_type(expr.type());
    return std::move(expr);
  }
  else if(expr.id() == ID_this)
  {
    throw errort().with_location(expr.source_location())
      << "'this' outside of method";
  }
  else if(expr.id() == ID_verilog_null)
  {
    return constant_exprt{ID_NULL, typet{ID_verilog_null}}.with_source_location(
      expr.source_location());
  }
  else
  {
    throw errort().with_location(expr.source_location())
      << "no conversion for no-operand expression " << expr.id();
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::resolve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const symbolt *verilog_typecheck_exprt::resolve(const irep_idt base_name)
{
  // in a task or function? Try local ones first
  if(function_or_task_name!="")
  {
    auto full_identifier =
      id2string(function_or_task_name) + "." + id2string(base_name);

    const symbolt *symbol;
    if(!ns.lookup(full_identifier, symbol))
      return symbol; // found!
  }

  // try named blocks, beginning with inner one
  for(named_blockst::const_reverse_iterator
      it=named_blocks.rbegin();
      it!=named_blocks.rend();
      it++)
  {
    auto full_identifier = id2string(module_identifier) + "." + id2string(*it) +
                           id2string(base_name);

    const symbolt *symbol;
    if(!ns.lookup(full_identifier, symbol))
      return symbol; // found!
  }

  auto full_identifier =
    id2string(module_identifier) + "." + id2string(base_name);

  const symbolt *symbol;
  if(!ns.lookup(full_identifier, symbol))
    return symbol; // found!

  // give up
  return nullptr;
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::convert_verilog_identifier(
  verilog_identifier_exprt expr,
  const std::optional<typet> &implicit_net_type)
{
  auto base_name = expr.base_name();
  auto symbol = resolve(base_name);

  if(symbol != nullptr)
  { 
    // found!
    if(
      symbol->type.id() == ID_to_be_elaborated ||
      symbol->type.id() == ID_elaborating)
    {
      // A parameter, or enum. The type is elaborated recursively.
      elaborate_symbol_rec(symbol->name);
      return symbol->symbol_expr().with_source_location(expr);
    }
    else if(symbol->type.id() == ID_verilog_genvar)
    {
      // This must be a constant.
      mp_integer int_value = genvar_value(base_name);

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
    else if(
      symbol->type.id() == ID_verilog_sva_named_sequence ||
      symbol->type.id() == ID_verilog_sva_named_property)
    {
      // A named sequence or property. Create an instance expression,
      // and then flatten it.
      auto symbol_expr = symbol->symbol_expr().with_source_location(expr);
      auto &declaration =
        to_verilog_sequence_property_declaration_base(symbol->value);
      auto instance =
        sva_sequence_property_instance_exprt{symbol_expr, {}, declaration}
          .with_source_location(expr);
      return flatten_named_sequence_property(instance);
    }
    else
    {
      return symbol->symbol_expr().with_source_location(expr);
    }
  }
  else
  {
    if(implicit_net_type.has_value())
    {
      implicit_wire(base_name, symbol, implicit_net_type.value());
      if(warn_implicit_nets)
      {
        warning().source_location = expr.source_location();
        warning() << "implicit wire " << symbol->display_name() << eom;
      }
      return symbol->symbol_expr().with_source_location(expr);
    }
    else
    {
      throw errort().with_location(expr.source_location())
        << "unknown identifier " << base_name;
    }
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

  DATA_INVARIANT(
    expr.rhs().id() == ID_verilog_identifier,
    "expected verilog_identifier as rhs of `.'");

  const irep_idt &rhs_base_name = expr.rhs().base_name();

  if(expr.lhs().type().id() == ID_struct || expr.lhs().type().id() == ID_union)
  {
    // look up the component
    auto &compound_type = to_struct_union_type(expr.lhs().type());
    auto &component = compound_type.get_component(rhs_base_name);
    if(component.is_nil())
      throw errort().with_location(expr.source_location())
        << compound_type.id() << " does not have a member named "
        << rhs_base_name;

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
      id2string(module) + "." + id2string(rhs_base_name);

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
        << "identifier `" << rhs_base_name << "' not found in module `"
        << module_instance_symbol->pretty_name << "'";
    }

    // We remember the identifier of the symbol.
    expr.identifier(full_identifier);

    return std::move(expr);
  }
  else if(expr.lhs().type().id() == ID_named_block)
  {
    const irep_idt full_identifier =
      id2string(lhs_identifier) + "." + id2string(rhs_base_name);

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
        << "identifier `" << rhs_base_name << "' not found in named block";
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
  auto source_location = expr.source_location();

  if(expr.type().id()==ID_string)
  {
    auto result = convert_string_literal(expr.get_value());
    // only add a typecast for now
    return typecast_exprt{std::move(expr), std::move(result.type())};
  }
  else if(expr.type().id()==ID_unsignedbv ||
          expr.type().id()==ID_signedbv ||
          expr.type().id()==ID_verilog_signedbv ||
          expr.type().id()==ID_verilog_unsignedbv)
  {
    // done already
    return std::move(expr);
  }

  const std::string &value = id2string(expr.get_value());

  // real or integer?
  if(
    value.find('.') != std::string::npos ||
    (value.find('h') == std::string::npos &&
     value.find('e') != std::string::npos)) // real?
  {
    auto result = convert_real_literal(value);
    result.add_source_location() = source_location;
    result.set("#verilog_value", value);

    return std::move(result);
  }
  else
  {
    auto result = convert_integral_literal(value);
    result.add_source_location() = source_location;
    result.set("#verilog_value", value);

    return std::move(result);
  }
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

  exprt tmp = elaborate_constant_expression_check(expr);

  if(tmp.id() == ID_infinity)
  {
    throw errort().with_location(source_location)
      << "expected integer constant, but got $";
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
  auto expr_lowered = verilog_lowering(std::move(expr));

  // replace constant symbols
  auto expr_replaced =
    elaborate_constant_expression_rec(std::move(expr_lowered));

  // finally simplify
  auto expr_simplified = verilog_simplifier(std::move(expr_replaced), ns);

  return expr_simplified;
}

/*******************************************************************\

Function: verilog_typecheck_exprt::elaborate_constant_expression_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::elaborate_constant_expression_rec(exprt expr)
{
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
      // Elaborate recursively
      elaborate_symbol_rec(symbol.name);

      // A parameter or local parameter. Replace by its value.
      return symbol.value;
    }

    exprt value=var_value(identifier);
    
    #if 0
    status() << "READ " << identifier << " = " << to_string(value) << eom;
    #endif

    if(value.is_not_nil())
    {
      source_locationt source_location = expr.source_location();
      exprt tmp = value;
      tmp.add_source_location() = source_location;
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
    // Do any operands first.
    for(auto &op : expr.operands())
    {
      // recursive call
      op = elaborate_constant_expression_rec(op);
    }
    return expr;
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::elaborate_constant_expression_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheck_exprt::elaborate_constant_expression_check(exprt expr)
{
  source_locationt source_location = expr.find_source_location();

  exprt tmp = elaborate_constant_expression(std::move(expr));

  // $ counts as a constant
  if(!tmp.is_constant() && tmp.id() != ID_infinity)
  {
    throw errort().with_location(source_location)
      << "expected constant expression, but got `" << to_string(tmp) << '\'';
  }

  return tmp;
}

/*******************************************************************\

Function: verilog_typecheck_exprt::elaborate_constant_integer_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer
verilog_typecheck_exprt::elaborate_constant_integer_expression(exprt expr)
{
  source_locationt source_location = expr.find_source_location();

  exprt tmp = elaborate_constant_expression(std::move(expr));

  if(!tmp.is_constant())
  {
    throw errort().with_location(source_location)
      << "expected constant integer expression, but got `" << to_string(tmp)
      << '\'';
  }

  return numeric_cast_v<mp_integer>(to_constant_expr(tmp));
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
  PRECONDITION(function.id() == ID_verilog_identifier);
  auto &base_name = to_verilog_identifier_expr(function).base_name();
  auto &arguments = expr.arguments();

  if(base_name == "$bits")
  {
    DATA_INVARIANT(arguments.size() == 1, "$bits has one argument");
    return bits(arguments[0]);
  }
  else if(base_name == "$low")
  {
    DATA_INVARIANT(arguments.size() == 1, "$low has one argument");
    return low(arguments[0]);
  }
  else if(base_name == "$high")
  {
    DATA_INVARIANT(arguments.size() == 1, "$high has one argument");
    return high(arguments[0]);
  }
  else if(base_name == "$left")
  {
    DATA_INVARIANT(arguments.size() == 1, "$left has one argument");
    return left(arguments[0]);
  }
  else if(base_name == "$right")
  {
    DATA_INVARIANT(arguments.size() == 1, "$right has one argument");
    return right(arguments[0]);
  }
  else if(base_name == "$increment")
  {
    DATA_INVARIANT(arguments.size() == 1, "$increment has one argument");
    return increment(arguments[0]);
  }
  else if(base_name == "$countones")
  {
    DATA_INVARIANT(arguments.size() == 1, "$countones has one argument");

    auto op = elaborate_constant_expression(arguments[0]);

    if(!op.is_constant())
      return std::move(expr); // give up

    return countones(to_constant_expr(op));
  }
  else if(base_name == "$clog2")
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
  else if(base_name == "$typename")
  {
    DATA_INVARIANT(arguments.size() == 1, "$typename takes one argument");
    return typename_string(arguments[0]);
  }
  else if(base_name == "$isunknown")
  {
    DATA_INVARIANT(arguments.size() == 1, "$isunknown takes one argument");

    auto op = elaborate_constant_expression(arguments[0]);

    if(!op.is_constant())
      return std::move(expr); // give up
    else
      return isunknown(to_constant_expr(op));
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

  auto integer_opt = is_constant_integer_post_convert(tmp);
  if(integer_opt.has_value())
  {
    value = integer_opt.value();
    return true;
  }
  else
    return false;
}

/*******************************************************************\

Function: verilog_typecheck_exprt::is_constant_integer_post_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::optional<mp_integer>
verilog_typecheck_exprt::is_constant_integer_post_convert(const exprt &expr)
{
  exprt tmp = expr;

  ns.follow_macros(tmp);
  tmp = simplify_expr(tmp, ns);

  if(!tmp.is_constant())
    return {};

  if(tmp.is_true())
    return 1;
  else if(tmp.is_false())
    return 0;
  else
    return numeric_cast<mp_integer>(to_constant_expr(tmp));
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

  auto &verilog_dest_type = dest_type.get(ID_C_verilog_type);
  if(verilog_dest_type == ID_verilog_enum)
  {
    // IEEE 1800-2017 6.19.3: "a variable of type enum cannot be directly
    // assigned a value that lies outside the enumeration set unless an
    // explicit cast is used"
    const typet &src_type = expr.type();

    if(
      src_type.get(ID_C_verilog_type) != ID_verilog_enum ||
      src_type.get(ID_C_identifier) != dest_type.get(ID_C_identifier))
    {
      throw errort().with_location(expr.source_location())
        << "assignment to enum requires enum of the same type, but got "
        << to_string(expr.type());
    }
  }

  if(expr.type() == dest_type)
    return;

  // do enum, union and struct decay
  enum_decay(expr);
  struct_decay(expr);
  union_decay(expr);

  const typet &src_type = expr.type();

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
    src_type.id() == ID_verilog_signedbv || src_type.id() == ID_verilog_integer)
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
        DATA_INVARIANT(value.size() != 0, "no empty bitvector");
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
    else if(
      dest_type.id() == ID_verilog_realtime ||
      dest_type.id() == ID_verilog_real ||
      dest_type.id() == ID_verilog_shortreal)
    {
      expr = typecast_exprt{expr, dest_type};
      return;
    }
    else if(dest_type.id() == ID_struct || dest_type.id() == ID_union)
    {
      // bit-vectors can be converted to
      // packed structs and packed unions
      expr = typecast_exprt{expr, dest_type};
      return;
    }
  }
  else if(src_type.id() == ID_verilog_real)
  {
    if(
      dest_type.id() == ID_verilog_realtime ||
      dest_type.id() == ID_verilog_shortreal)
    {
      // The rounding mode, if needed, is added during lowering.
      expr = typecast_exprt{expr, dest_type};
      return;
    }
    else if(
      dest_type.id() == ID_bool || dest_type.id() == ID_signedbv ||
      dest_type.id() == ID_unsignedbv)
    {
      // Cast from float to int -- the rounding mode is added during lowering.
      expr = typecast_exprt{expr, dest_type};
      return;
    }
  }
  else if(src_type.id() == ID_verilog_null)
  {
    if(
      dest_type.id() == ID_verilog_chandle ||
      dest_type.id() == ID_verilog_class_type ||
      dest_type.id() == ID_verilog_event)
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
  if(expr.type().id() == ID_verilog_sva_sequence)
  {
    throw errort{}.with_location(expr.source_location())
      << "cannot use SVA sequence as an expression";
  }
  else if(expr.type().id() == ID_verilog_sva_property)
  {
    throw errort{}.with_location(expr.source_location())
      << "cannot use SVA property as an expression";
  }
  else if(expr.type().id() != ID_bool)
  {
    // everything else can be converted to Boolean
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

verilog_typecheck_exprt::ranget
verilog_typecheck_exprt::convert_range(const exprt &range)
{
  if(range.operands().size()!=2)
  {
    throw errort().with_location(range.source_location())
      << "range expected to have two operands";
  }

  auto &binary_expr = to_binary_expr(range);

  return ranget{
    convert_integer_constant_expression(binary_expr.op0()),
    convert_integer_constant_expression(binary_expr.op1())};
}

/*******************************************************************\

Function: verilog_typecheck_exprt::enum_decay

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet verilog_typecheck_exprt::enum_decay(const typet &type)
{
  // Verilog enum types decay to their base type when used in relational
  // or arithmetic expressions.
  if(type.get(ID_C_verilog_type) == ID_verilog_enum)
  {
    typet result = type;
    result.remove(ID_C_verilog_type);
    result.remove(ID_C_identifier);
    return result;
  }
  else
    return type;
}

/*******************************************************************\

Function: verilog_typecheck_exprt::enum_decay

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::enum_decay(exprt &expr) const
{
  // Verilog enum types decay to their base type when used in relational
  // or arithmetic expressions.
  if(expr.type().get(ID_C_verilog_type) == ID_verilog_enum)
  {
    expr = typecast_exprt{expr, enum_decay(expr.type())};
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::union_decay

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::union_decay(exprt &expr) const
{
  // 1800-2017 7.3.1
  // Verilog union types decay to a vector type [$bits(t)-1:0] when
  // used in relational or arithmetic expressions.
  auto &type = expr.type();
  if(type.id() == ID_union)
  {
    auto new_type =
      unsignedbv_typet{numeric_cast_v<std::size_t>(get_width(type))};
    // The synthesis stage turns these typecasts into a member
    // expression.
    expr = typecast_exprt{expr, new_type};
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::struct_decay

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::struct_decay(exprt &expr) const
{
  // 1800-2017 7.2.1
  // Verilog packed struct types decay to a vector type [$bits(t)-1:0]
  // when used in relational or arithmetic expressions.
  auto &type = expr.type();
  if(type.id() == ID_struct && type.get_bool(ID_packed))
  {
    auto new_type =
      unsignedbv_typet{numeric_cast_v<std::size_t>(get_width(type))};
    expr = typecast_exprt{expr, new_type};
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
  // Follows 1800-2017 11.8.2.

  // First get the self-determined type and size of both operands
  union_decay(op0);
  union_decay(op1);

  enum_decay(op0);
  enum_decay(op1);

  struct_decay(op0);
  struct_decay(op1);

  // Now get the max
  const typet new_type = max_type(op0.type(), op1.type());

  if(new_type.is_nil())
  {
    throw errort().with_location(expr.source_location())
      << "expected operands of compatible type but got:\n"
      << "  " << to_string(op0.type()) << '\n'
      << "  " << to_string(op1.type());
  }

  // Now do downwards propagation
  downwards_type_propagation(op0, new_type);
  downwards_type_propagation(op1, new_type);
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_relation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheck_exprt::convert_relation(binary_exprt &expr)
{
  convert_expr(expr.lhs());
  convert_expr(expr.rhs());

  // determine the max of the operand types and propagate it downwards
  tc_binary_expr(expr);
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

  if(vt0.is_null() || vt1.is_chandle())
    return t1;

  if(vt0.is_chandle() || vt1.is_null())
    return t0;

  if(vt0.is_null() || vt1.is_event())
    return t1;

  if(vt0.is_event() || vt1.is_null())
    return t0;

  if(
    vt0.is_string() && (vt1.is_signed() || vt1.is_unsigned() ||
                        vt1.is_verilog_signed() || vt1.is_verilog_unsigned()))
  {
    return t0;
  }

  if(
    (vt0.is_signed() || vt0.is_unsigned() || vt0.is_verilog_signed() ||
     vt0.is_verilog_unsigned()) &&
    vt0.is_string())
  {
    return t1;
  }

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
  if(vt0.is_verilog_real())
    return t0;
  else if(vt1.is_verilog_real())
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

void verilog_typecheck_exprt::tc_binary_expr(binary_exprt &expr)
{
  tc_binary_expr(expr, expr.op0(), expr.op1());
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

    if(
      expr.op().type().id() == ID_verilog_signedbv ||
      expr.op().type().id() == ID_verilog_unsignedbv)
    {
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
    must_be_bit_vector(expr.op());

    if(
      expr.op().type().id() == ID_verilog_signedbv ||
      expr.op().type().id() == ID_verilog_unsignedbv)
    {
      expr.type()=verilog_unsignedbv_typet(1);
    }
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
  else if(expr.id() == ID_verilog_explicit_const_cast)
  {
    // SystemVerilog has got const'(expr).
    // This is an explicit type cast.
    convert_expr(expr.op());
    expr.type() = expr.op().type();
  }
  else if(expr.id() == ID_verilog_explicit_type_cast)
  {
    // SystemVerilog has got type'(expr). This is an explicit
    // type cast. These are assignment contexts.
    convert_expr(expr.op());
    expr.type() = elaborate_type(expr.type());

    // In contrast to assignments, these can turn integers into enums
    // (1800-2017 6.19.3).
    if(expr.type().get(ID_C_verilog_type) == ID_verilog_enum)
    {
      expr.op() = typecast_exprt::conditional_cast(expr.op(), expr.type());
    }
    else
    {
      assignment_conversion(expr.op(), expr.type());
    }

    CHECK_RETURN(expr.op().type() == expr.type());
  }
  else if(expr.id() == ID_verilog_explicit_signing_cast)
  {
    // SystemVerilog has got signed'(expr) and unsigned'(expr).
    // This is an explicit type cast.
    convert_expr(expr.op());
    const auto &old_type = expr.op().type();
    const auto dest_type = expr.type().id();
    PRECONDITION(dest_type == ID_signed || dest_type == ID_unsigned);

    if(old_type.id() == ID_signedbv)
    {
      if(dest_type == ID_unsigned)
        expr.type() = unsignedbv_typet{to_signedbv_type(old_type).get_width()};
      else
        expr.type() = old_type; // leave as is
    }
    else if(old_type.id() == ID_verilog_signedbv)
    {
      if(dest_type == ID_unsigned)
        expr.type() = verilog_unsignedbv_typet{
          to_verilog_signedbv_type(old_type).get_width()};
      else
        expr.type() = old_type; // leave as is
    }
    else if(old_type.id() == ID_unsignedbv)
    {
      if(dest_type == ID_signed)
        expr.type() = signedbv_typet{to_unsignedbv_type(old_type).get_width()};
      else
        expr.type() = old_type; // leave as is
    }
    else if(old_type.id() == ID_verilog_unsignedbv)
    {
      if(dest_type == ID_signed)
        expr.type() = verilog_signedbv_typet{
          to_verilog_unsignedbv_type(old_type).get_width()};
      else
        expr.type() = old_type; // leave as is
    }
    else if(old_type.id() == ID_bool)
    {
      if(dest_type == ID_signed)
        expr.type() = signedbv_typet{1};
      else
        expr.type() = old_type; // leave as is
    }
    else
    {
      throw errort().with_location(expr.source_location())
        << "signing cast expects a scalar operand";
    }
  }
  else if(expr.id() == ID_verilog_implicit_typecast)
  {
    // We generate implict casts during elaboration.
    expr.type() = elaborate_type(expr.type());
    convert_expr(expr.op());
    expr.id(ID_typecast);
  }
  else if(
    expr.id() == ID_verilog_streaming_concatenation_left_to_right ||
    expr.id() == ID_verilog_streaming_concatenation_right_to_left)
  {
    // slice_size is defaulted to 1
    PRECONDITION(expr.op().operands().size() == 1);
    convert_expr(expr.op().operands()[0]);
    must_be_bit_vector(expr.op().operands()[0]);
    expr.type() = expr.op().operands()[0].type();
    return std::move(expr);
  }
  else if(expr.id() == ID_bitnot)
  {
    convert_expr(expr.op());
    expr.type() = expr.op().type();

    // Boolean?
    if(expr.type().id() == ID_bool)
      expr.id(ID_not);
  }
  else if(expr.id() == ID_posedge || expr.id() == ID_negedge)
  {
    convert_expr(expr.op());

    // 1800-2017 6.12.1
    // Edge event controls must not be given real operands.
    if(
      expr.op().type().id() == ID_verilog_shortreal ||
      expr.op().type().id() == ID_verilog_real)
    {
      throw errort().with_location(expr.source_location())
        << "edge event controls do not take real operands";
    }

    expr.type() = bool_typet{};
  }
  else if(expr.id() == ID_verilog_smv_eventually)
  {
    convert_expr(expr.op());
    make_boolean(expr.op());
    expr.type() = bool_typet{};
  }
  else if(
    expr.id() == ID_postincrement || expr.id() == ID_preincrement ||
    expr.id() == ID_postdecrement || expr.id() == ID_predecrement)
  {
    convert_expr(expr.op());
    expr.type() = expr.op().type();
  }
  else if(expr.id() == ID_verilog_new)
  {
    // The type of these expressions is determined by their context.
    expr.type() = typet(ID_verilog_new);
  }
  else if(expr.id() == ID_member_initializer)
  {
    // assignment patterns, 1800 2017 10.9
    convert_expr(expr.op());
  }
  else if(expr.id() == ID_verilog_tagged_union)
  {
    throw errort{}.with_location(expr.source_location())
      << "no support for tagged unions";
  }
  else
  {
    throw errort() << "no conversion for unary expression " << expr.id();
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
  exprt &op0 = expr.op0(), &op1 = expr.op1();
  convert_expr(op0);
  convert_expr(op1);

  if(op0.type().id() == ID_verilog_real)
  {
    throw errort().with_location(op0.source_location())
      << "bit-select of real is not allowed";
  }

  if(op1.type().id() == ID_verilog_real)
  {
    throw errort().with_location(op1.source_location())
      << "real number index is not allowed";
  }

  if(op0.type().id() == ID_array)
  {
    typet _index_type = index_type(to_array_type(op0.type()));
    op1 = typecast_exprt{op1, _index_type};

    expr.type() = to_array_type(op0.type()).element_type();
    expr.id(ID_index);
  }
  else
  {
    // extractbit works on bit vectors only
    no_bool_ops(expr);

    auto width = get_width(op0.type());
    auto offset = op0.type().get_int(ID_C_offset);

    auto op1_opt = is_constant_integer_post_convert(op1);

    if(op1_opt.has_value()) // constant index
    {
      // 1800-2017 sec 11.5.1: out-of-bounds bit-select is
      // x for 4-state and 0 for 2-state values.
      auto op1_int = op1_opt.value();

      if(op1_int < offset || op1_int >= width + offset)
        return false_exprt().with_source_location(expr);

      op1_int -= offset;

      if(op0.type().get_bool(ID_C_increasing))
        op1_int = width - op1_int - 1;

      expr.op1() = from_integer(op1_int, natural_typet());
    }
    else // non-constant index
    {
      if(offset != 0)
      {
        expr.op1() =
          minus_exprt{expr.op1(), from_integer(offset, expr.op1().type())};
      }

      if(op0.type().get_bool(ID_C_increasing))
      {
        expr.op1() =
          minus_exprt{from_integer(width - 1, expr.op1().type()), expr.op1()};
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
  must_be_bit_vector(op1);

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

exprt verilog_typecheck_exprt::convert_power_expr(power_exprt expr)
{
  convert_expr(expr.op0());
  convert_expr(expr.op1());

  no_bool_ops(expr);

  // Is one of the operands four-valued?
  if(is_four_valued(expr.op0().type()))
  {
    // We make the other operand also four-valued, if needed
    expr.op1() = typecast_exprt{expr.op1(), four_valued(expr.op1().type())};
  }
  else if(is_four_valued(expr.op1().type()))
  {
    // We make the other operand also four-valued, if needed
    expr.op0() = typecast_exprt{expr.op0(), four_valued(expr.op0().type())};
  }

  // 1800-2017 Table 11-21
  // The width of a power is the width of the left operand
  expr.type() = expr.op0().type();

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
  convert_expr(expr.lhs());
  convert_expr(expr.rhs());

  no_bool_ops(expr);

  const typet &lhs_type = expr.lhs().type();
  const typet &rhs_type = expr.rhs().type();

  // The bit width of a shift is always the bit width of the left operand.
  // The result is four-valued if either of the operands is four-valued.
  if(is_four_valued(lhs_type))
    expr.type() = lhs_type;
  else if(is_four_valued(rhs_type))
    expr.type() = four_valued(lhs_type);
  else
    expr.type() = lhs_type;

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
  else if(expr.id() == ID_verilog_package_scope)
  {
    auto location = expr.source_location();
    auto &package_scope = to_verilog_package_scope_expr(expr);

    if(package_scope.identifier().id() != ID_verilog_identifier)
      throw errort().with_location(location)
        << expr.id() << " expects verilog_identifier on the rhs";

    auto package_base = package_scope.package_base_name();
    auto rhs_base =
      to_verilog_identifier_expr(package_scope.identifier()).base_name();

    // stitch together
    irep_idt full_identifier =
      id2string(verilog_package_identifier(expr.lhs().id())) + '.' +
      id2string(rhs_base);

    const symbolt *symbol;
    if(ns.lookup(full_identifier, symbol))
    {
      throw errort().with_location(location)
        << "identifier " << rhs_base << " not found in package "
        << package_base;
    }

    // found!
    return symbol_exprt{full_identifier, symbol->type}.with_source_location(
      location);
  }
  else if(expr.id()==ID_replication)
    return convert_replication_expr(to_replication_expr(expr));
  else if(expr.id() == ID_and || expr.id() == ID_or)
  {
    Forall_operands(it, expr)
    {
      convert_expr(*it);
      make_boolean(*it);
    }

    expr.type()=bool_typet();

    return std::move(expr);
  }
  else if(expr.id() == ID_verilog_iff || expr.id() == ID_verilog_implies)
  {
    // 1800 2017 11.4.7 Logical operators
    convert_expr(expr.lhs());
    convert_expr(expr.rhs());

    // These return 'x' if either of the operands contains x or z.
    if(
      expr.lhs().type().id() == ID_verilog_signedbv ||
      expr.lhs().type().id() == ID_verilog_unsignedbv ||
      expr.rhs().type().id() == ID_verilog_signedbv ||
      expr.rhs().type().id() == ID_verilog_unsignedbv)
    {
      // Four-valued case.
      expr.type() = verilog_unsignedbv_typet{1};
    }
    else // Two-valued case.
      expr.type() = bool_typet{};

    return std::move(expr);
  }
  else if(expr.id()==ID_equal || expr.id()==ID_notequal)
  {
    expr.type()=bool_typet();

    convert_relation(expr);

    return std::move(expr);
  }
  else if(
    expr.id() == ID_verilog_logical_equality ||
    expr.id() == ID_verilog_logical_inequality)
  {
    // == and !=
    convert_relation(expr);

    // This returns 'x' if either of the operands contains x or z.
    if(
      expr.lhs().type().id() == ID_verilog_signedbv ||
      expr.lhs().type().id() == ID_verilog_unsignedbv ||
      expr.rhs().type().id() == ID_verilog_signedbv ||
      expr.rhs().type().id() == ID_verilog_unsignedbv)
    {
      // Four-valued case. The ID stays
      // ID_verilog_logical_equality or
      // ID_verilog_logical_inequality.
      expr.type() = verilog_unsignedbv_typet(1);
    }
    else
    {
      // On two-valued logic, it's the same as proper equality.
      expr.type() = bool_typet();
      if(expr.id() == ID_verilog_logical_equality)
        expr.id(ID_equal);
      else
        expr.id(ID_notequal);
    }

    return std::move(expr);
  }
  else if(
    expr.id() == ID_verilog_wildcard_equality ||
    expr.id() == ID_verilog_wildcard_inequality)
  {
    // ==? and !=?
    // 1800-2017 Table 11-1 says that any integral operands are allowed;
    // however, it is unclear how these would apply to types that do not have
    // a bit-encoding.
    convert_relation(expr);

    must_be_bit_vector(expr.lhs());
    must_be_bit_vector(expr.rhs());

    expr.type() = verilog_unsignedbv_typet{1};

    return std::move(expr);
  }
  else if(expr.id()==ID_verilog_case_equality ||
          expr.id()==ID_verilog_case_inequality)
  {
    // === and !==
    // Take any operand types except real and shortreal (1800-2017 Table 11-1).
    // The result is always Boolean, and semantically
    // a proper equality is performed.
    expr.type() = bool_typet{};

    convert_relation(expr);

    if(
      expr.lhs().type().id() == ID_verilog_real ||
      expr.lhs().type().id() == ID_verilog_shortreal)
    {
      throw errort().with_location(expr.source_location())
        << "the case equality operator does not allow real or shortreal";
    }

    return std::move(expr);
  }
  else if(expr.id()==ID_lt || expr.id()==ID_gt ||
          expr.id()==ID_le || expr.id()==ID_ge)
  {
    convert_relation(expr);
    no_bool_ops(expr);

    // This returns 'x' if either of the operands contains x or z.
    if(is_four_valued(expr.lhs().type()) || is_four_valued(expr.rhs().type()))
    {
      expr.type() = verilog_unsignedbv_typet(1);
    }
    else
    {
      expr.type() = bool_typet{};
    }

    return std::move(expr);
  }
  else if(expr.id() == ID_power)
    return convert_power_expr(to_power_expr(expr));
  else if(expr.id()==ID_shl)
    return convert_shl_expr(to_shl_expr(expr));
  else if(expr.id()==ID_shr)
  {
    // This is the >>> expression, which turns into ID_lshr or ID_ashr
    // depending on type of first operand.

    convert_expr(expr.lhs());
    convert_expr(expr.rhs());
    must_be_bit_vector(expr.lhs());
    must_be_bit_vector(expr.rhs());
    no_bool_ops(expr);

    const typet &lhs_type = expr.lhs().type();
    const typet &rhs_type = expr.rhs().type();

    if(
      lhs_type.id() == ID_signedbv || lhs_type.id() == ID_verilog_signedbv ||
      lhs_type.id() == ID_integer)
    {
      expr.id(ID_ashr);
    }
    else
      expr.id(ID_lshr);

    // The bit width of a shift is always the bit width of the left operand.
    // The result is four-valued if either of the operands is four-valued.
    if(is_four_valued(lhs_type))
      expr.type() = lhs_type;
    else if(is_four_valued(rhs_type))
      expr.type() = four_valued(lhs_type);
    else
      expr.type() = lhs_type;

    return std::move(expr);
  }
  else if(expr.id()==ID_ashr)
  {
    // would only happen when re-typechecking, otherwise see above
    DATA_INVARIANT(false, "no re-typechecking");
  }
  else if(expr.id()==ID_lshr)
  {
    // logical right shift >>
    convert_expr(expr.lhs());
    convert_expr(expr.rhs());
    must_be_bit_vector(expr.lhs());
    must_be_bit_vector(expr.rhs());

    const typet &lhs_type = expr.lhs().type();
    const typet &rhs_type = expr.rhs().type();

    // The bit width of a shift is always the bit width of the left operand.
    // The result is four-valued if either of the operands is four-valued.
    if(is_four_valued(lhs_type))
      expr.type() = lhs_type;
    else if(is_four_valued(rhs_type))
      expr.type() = four_valued(lhs_type);
    else
      expr.type() = lhs_type;

    return std::move(expr);
  }
  else if(expr.id() == ID_div)
  {
    Forall_operands(it, expr)
      convert_expr(*it);

    tc_binary_expr(expr);
    no_bool_ops(expr);

    expr.type()=expr.op0().type();

    return std::move(expr);
  }
  else if(expr.id() == ID_mod)
  {
    convert_expr(expr.lhs());
    convert_expr(expr.rhs());

    tc_binary_expr(expr);
    no_bool_ops(expr);

    must_be_bit_vector(expr.lhs());
    must_be_bit_vector(expr.rhs());

    expr.type() = expr.lhs().type();

    return std::move(expr);
  }
  else if(expr.id()==ID_hierarchical_identifier)
  {
    return convert_hierarchical_identifier(
      to_hierarchical_identifier_expr(std::move(expr)));
  }
  else if(expr.id() == ID_verilog_explicit_size_cast)
  {
    // SystemVerilog has got expr'(expr). This is an explicit
    // type cast, to change the size (in bits) of the rhs to the
    // number given as lhs.
    convert_expr(expr.rhs());
    auto new_size = convert_integer_constant_expression(expr.lhs());
    expr.lhs() = from_integer(new_size, natural_typet{});
    auto new_size_int = numeric_cast_v<std::size_t>(new_size);
    auto &op_type = expr.rhs().type();

    if(op_type.id() == ID_signedbv)
    {
      expr.type() = signedbv_typet{new_size_int};
    }
    else if(op_type.id() == ID_verilog_signedbv)
    {
      expr.type() = verilog_signedbv_typet{new_size_int};
    }
    else if(op_type.id() == ID_unsignedbv || op_type.id() == ID_bool)
    {
      expr.type() = unsignedbv_typet{new_size_int};
    }
    else if(op_type.id() == ID_verilog_unsignedbv)
    {
      expr.type() = verilog_unsignedbv_typet{new_size_int};
    }
    else
    {
      throw errort().with_location(expr.source_location())
        << "cannot perform size cast on " << to_string(op_type);
    }

    // These act like an assignment (1800-2017 6.24.1)
    assignment_conversion(expr.rhs(), expr.type());

    CHECK_RETURN(expr.rhs().type() == expr.type());

    return std::move(expr);
  }
  else if(
    expr.id() == ID_verilog_streaming_concatenation_left_to_right ||
    expr.id() == ID_verilog_streaming_concatenation_right_to_left)
  {
    auto slice_size = convert_integer_constant_expression(expr.op0());

    if(slice_size < 1)
    {
      // 1800-2017 11.4.14.2 "it shall be an error for the
      // value of the expression to be zero or negative"
      throw errort().with_location(expr.source_location())
        << "size slice must be 1 or greater";
    }

    expr.op0() = from_integer(slice_size, natural_typet());

    convert_expr(expr.op0());
    PRECONDITION(expr.op1().operands().size() == 1);
    for(auto &op : expr.op1().operands())
      convert_expr(op);
    expr.type() = expr.op1().operands().front().type();

    return std::move(expr);
  }
  else if(expr.id() == ID_verilog_inside)
  {
    convert_expr(expr.op0());
    for(auto &op : expr.op1().operands())
    {
      convert_expr(op);
      if(op.id() == ID_verilog_value_range)
      {
        auto &value_range = to_verilog_value_range_expr(op);
        tc_binary_expr(expr, value_range.lhs(), op);
        tc_binary_expr(expr, value_range.rhs(), op);
      }
      else
        tc_binary_expr(expr, expr.op0(), op);
    }
    expr.type() = bool_typet{};
    return std::move(expr);
  }
  else if(expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult)
  {
    for(auto &op : expr.operands())
      convert_expr(op);

    tc_binary_expr(expr);

    no_bool_ops(expr);

    expr.type() = expr.op0().type();
    return std::move(expr);
  }
  else if(
    expr.id() == ID_bitand || expr.id() == ID_bitor || expr.id() == ID_bitxor ||
    expr.id() == ID_bitxnor || expr.id() == ID_bitnand ||
    expr.id() == ID_bitnor)
  {
    for(auto &op : expr.operands())
      convert_expr(op);

    tc_binary_expr(expr);

    expr.type() = expr.op0().type();

    // Boolean?
    if(expr.type().id() == ID_bool)
    {
      if(expr.id() == ID_bitand)
        expr.id(ID_and);
      else if(expr.id() == ID_bitor)
        expr.id(ID_or);
      else if(expr.id() == ID_bitxor)
        expr.id(ID_xor);
      else if(expr.id() == ID_bitxnor)
        expr.id(ID_equal);
      else if(expr.id() == ID_bitnand)
        expr.id(ID_nand);
      else if(expr.id() == ID_bitnor)
        expr.id(ID_nor);
    }

    return std::move(expr);
  }
  else if(expr.id() == ID_and || expr.id() == ID_or)
  {
    for(auto &op : expr.operands())
    {
      convert_expr(op);
      make_boolean(op);
    }

    tc_binary_expr(expr);

    expr.type() = expr.op0().type();

    return std::move(expr);
  }
  else if(
    expr.id() == ID_xor || expr.id() == ID_xnor || expr.id() == ID_nand ||
    expr.id() == ID_nor)
  {
    // should not occur -- only generated by the typechecker
    PRECONDITION(false);
  }
  else if(expr.id() == ID_verilog_value_range)
  {
    for(auto &op : expr.operands())
      convert_expr(op);
    expr.type() = expr.op0().type();
    return std::move(expr);
  }
  else
  {
    throw errort().with_location(expr.source_location())
      << "no conversion for binary expression " << expr.id();
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

    // store these back onto the expression
    expr.op1() = from_integer(msb, integer_typet())
                   .with_source_location(expr.op1().source_location());
    expr.op2() = from_integer(lsb, integer_typet())
                   .with_source_location(expr.op2().source_location());

    // Part-select expressions are unsigned, even if the
    // op0 is signed and the entire expression is selected!
    auto expr_type =
      unsignedbv_typet{numeric_cast_v<std::size_t>(msb - lsb + 1)};

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

    part_select.width() = from_integer(width, integer_typet());

    // Part-select expressions are unsigned, even if the
    // entire expression is selected!
    expr.type() = unsignedbv_typet{numeric_cast_v<std::size_t>(width)};

    return std::move(expr);
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
  verilog_standardt standard,
  message_handlert &message_handler,
  const namespacet &ns)
{
  const unsigned errors_before=
    message_handler.get_message_count(messaget::M_ERROR);

  verilog_typecheck_exprt verilog_typecheck_expr(
    standard, true, ns, module_identifier, message_handler);

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
