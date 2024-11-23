/*******************************************************************\

Module: Verilog Expression Simplifier

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_simplifier.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/mathematical_types.h>
#include <util/simplify_expr.h>

#include <ebmc/ebmc_error.h>

#include "verilog_types.h"

static constant_exprt
countones(const constant_exprt &expr, const namespacet &ns)
{
  // lower to popcount and try simplifier
  auto simplified =
    simplify_expr(popcount_exprt{expr, verilog_int_typet{}.lower()}, ns);

  if(!simplified.is_constant())
  {
    throw ebmc_errort() << "failed to simplify constant $countones";
  }
  else
    return to_constant_expr(simplified);
}

static exprt verilog_simplifier_rec(exprt expr, const namespacet &ns)
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
    op = verilog_simplifier_rec(op, ns);
    if(!op.is_constant())
      operands_are_constant = false;
  }

  // Are all operands constants now?
  if(!operands_are_constant)
    return expr; // give up

  auto make_all_ones = [](const typet &type) -> exprt
  {
    if(type.id() == ID_unsignedbv)
    {
      return from_integer(
        power(2, to_unsignedbv_type(type).get_width()) - 1, type);
    }
    else if(type.id() == ID_signedbv)
    {
      return from_integer(-1, type);
    }
    else if(type.id() == ID_bool)
      return true_exprt{};
    else
      PRECONDITION(false);
  };

  if(expr.id() == ID_reduction_or)
  {
    // The simplifier doesn't know how to simplify reduction_or
    auto &reduction_or = to_unary_expr(expr);
    expr = notequal_exprt(
      reduction_or.op(), from_integer(0, reduction_or.op().type()));
  }
  else if(expr.id() == ID_reduction_nor)
  {
    // The simplifier doesn't know how to simplify reduction_nor
    auto &reduction_nor = to_unary_expr(expr);
    expr = equal_exprt(
      reduction_nor.op(), from_integer(0, reduction_nor.op().type()));
  }
  else if(expr.id() == ID_reduction_and)
  {
    // The simplifier doesn't know how to simplify reduction_and
    auto &reduction_and = to_unary_expr(expr);
    expr =
      equal_exprt{reduction_and.op(), make_all_ones(reduction_and.op().type())};
  }
  else if(expr.id() == ID_reduction_nand)
  {
    // The simplifier doesn't know how to simplify reduction_nand
    auto &reduction_nand = to_unary_expr(expr);
    expr = notequal_exprt{
      reduction_nand.op(), make_all_ones(reduction_nand.op().type())};
  }
  else if(expr.id() == ID_reduction_xor)
  {
    // The simplifier doesn't know how to simplify reduction_xor
    // Lower to countones.
    auto &reduction_xor = to_unary_expr(expr);
    auto ones = countones(to_constant_expr(reduction_xor.op()), ns);
    expr = extractbit_exprt{ones, from_integer(0, natural_typet{})};
  }
  else if(expr.id() == ID_reduction_xnor)
  {
    // The simplifier doesn't know how to simplify reduction_xnor
    // Lower to countones.
    auto &reduction_xnor = to_unary_expr(expr);
    auto ones = countones(to_constant_expr(reduction_xnor.op()), ns);
    expr = not_exprt{extractbit_exprt{ones, from_integer(0, natural_typet{})}};
  }
  else if(expr.id() == ID_replication)
  {
    auto &replication = to_replication_expr(expr);
    auto times = numeric_cast_v<std::size_t>(replication.times());
    // lower to a concatenation
    exprt::operandst ops;
    ops.reserve(times);
    for(std::size_t i = 0; i < times; i++)
      ops.push_back(replication.op());
    expr = concatenation_exprt{ops, expr.type()};
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

exprt verilog_simplifier(exprt expr, const namespacet &ns)
{
  return verilog_simplifier_rec(expr, ns);
}
