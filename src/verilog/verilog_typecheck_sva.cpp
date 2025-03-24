/*******************************************************************\

Module: Typechecking for SVA

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/mathematical_types.h>

#include "sva_expr.h"
#include "verilog_typecheck_expr.h"

exprt verilog_typecheck_exprt::convert_unary_sva(unary_exprt expr)
{
  if(expr.id() == ID_sva_not)
  {
    convert_sva(expr.op());
    make_boolean(expr.op());
    expr.type() = bool_typet(); // always boolean, never x
    return std::move(expr);
  }
  else if(
    expr.id() == ID_sva_always || expr.id() == ID_sva_s_eventually ||
    expr.id() == ID_sva_cycle_delay_plus ||
    expr.id() == ID_sva_cycle_delay_star || expr.id() == ID_sva_weak ||
    expr.id() == ID_sva_strong || expr.id() == ID_sva_nexttime ||
    expr.id() == ID_sva_s_nexttime ||
    expr.id() == ID_sva_sequence_first_match ||
    expr.id() == ID_sva_sequence_repetition_plus ||
    expr.id() == ID_sva_sequence_repetition_star)
  {
    convert_sva(expr.op());
    make_boolean(expr.op());
    expr.type() = bool_typet();
    return std::move(expr);
  }
  else
  {
    // not SVA
    return convert_expr_rec(std::move(expr));
  }
}

exprt verilog_typecheck_exprt::convert_binary_sva(binary_exprt expr)
{
  if(
    expr.id() == ID_sva_and || expr.id() == ID_sva_or ||
    expr.id() == ID_sva_implies || expr.id() == ID_sva_iff)
  {
    for(auto &op : expr.operands())
    {
      convert_sva(op);
      make_boolean(op);
    }

    // always boolean, never x
    expr.type() = bool_typet();

    return std::move(expr);
  }
  else if(
    expr.id() == ID_sva_disable_iff || expr.id() == ID_sva_accept_on ||
    expr.id() == ID_sva_reject_on || expr.id() == ID_sva_sync_accept_on ||
    expr.id() == ID_sva_sync_reject_on)
  {
    convert_expr(to_sva_abort_expr(expr).condition());
    make_boolean(to_sva_abort_expr(expr).condition());
    convert_sva(to_sva_abort_expr(expr).property());
    make_boolean(to_sva_abort_expr(expr).property());
    expr.type() = bool_typet();
    return std::move(expr);
  }
  else if(expr.id() == ID_sva_indexed_nexttime)
  {
    convert_expr(to_sva_indexed_nexttime_expr(expr).index());

    auto &op = to_sva_indexed_nexttime_expr(expr).op();
    convert_sva(op);
    make_boolean(op);
    expr.type() = bool_typet();

    return std::move(expr);
  }
  else if(expr.id() == ID_sva_indexed_s_nexttime)
  {
    convert_expr(to_sva_indexed_s_nexttime_expr(expr).index());

    auto &op = to_sva_indexed_s_nexttime_expr(expr).op();
    convert_sva(op);
    make_boolean(op);
    expr.type() = bool_typet();

    return std::move(expr);
  }
  else if(
    expr.id() == ID_sva_overlapped_implication ||
    expr.id() == ID_sva_non_overlapped_implication ||
    expr.id() == ID_sva_overlapped_followed_by ||
    expr.id() == ID_sva_nonoverlapped_followed_by ||
    expr.id() == ID_sva_until || expr.id() == ID_sva_s_until ||
    expr.id() == ID_sva_until_with || expr.id() == ID_sva_s_until_with)
  {
    convert_sva(expr.op0());
    make_boolean(expr.op0());
    convert_sva(expr.op1());
    make_boolean(expr.op1());
    expr.type() = bool_typet();

    return std::move(expr);
  }
  else if(expr.id() == ID_sva_sequence_concatenation) // a ##b c
  {
    expr.type() = bool_typet();
    convert_sva(expr.op0());
    make_boolean(expr.op0());
    convert_sva(expr.op1());
    make_boolean(expr.op1());
    return std::move(expr);
  }
  else if(
    expr.id() == ID_sva_sequence_intersect ||
    expr.id() == ID_sva_sequence_throughout ||
    expr.id() == ID_sva_sequence_within ||
    expr.id() == ID_sva_sequence_first_match)
  {
    auto &binary_expr = to_binary_expr(expr);

    convert_sva(binary_expr.lhs());
    make_boolean(binary_expr.lhs());
    convert_sva(binary_expr.rhs());
    make_boolean(binary_expr.rhs());

    expr.type() = bool_typet();

    return std::move(expr);
  }
  else if(
    expr.id() == ID_sva_sequence_non_consecutive_repetition ||
    expr.id() == ID_sva_sequence_goto_repetition)
  {
    auto &binary_expr = to_binary_expr(expr);

    convert_sva(binary_expr.lhs());
    make_boolean(binary_expr.lhs());

    convert_sva(binary_expr.rhs());

    mp_integer n = elaborate_constant_integer_expression(binary_expr.rhs());
    if(n < 0)
      throw errort().with_location(binary_expr.rhs().source_location())
        << "number of repetitions must not be negative";

    binary_expr.rhs() = from_integer(n, integer_typet{});

    expr.type() = bool_typet();

    return std::move(expr);
  }
  else if(expr.id() == ID_sva_case)
  {
    auto &case_expr = to_sva_case_expr(expr);
    convert_expr(case_expr.case_op());

    for(auto &case_item : case_expr.case_items())
    {
      // same rules as case statement
      for(auto &pattern : case_item.patterns())
      {
        convert_expr(pattern);
        typet t = max_type(pattern.type(), case_expr.case_op().type());
        propagate_type(pattern, t);
      }

      convert_sva(case_item.result());
      make_boolean(case_item.result());
    }

    expr.type() = bool_typet();
    return std::move(expr);
  }
  else
  {
    // not SVA
    return convert_expr_rec(std::move(expr));
  }
}

exprt verilog_typecheck_exprt::convert_ternary_sva(ternary_exprt expr)
{
  if(expr.id() == ID_sva_cycle_delay) // ##[1:2] something
  {
    expr.type() = bool_typet();

    convert_expr(expr.op0());
    elaborate_constant_expression_check(expr.op0());

    if(expr.op1().is_not_nil())
    {
      convert_expr(expr.op1());
      elaborate_constant_expression_check(expr.op1());
    }

    convert_sva(expr.op2());
    make_boolean(expr.op2());

    return std::move(expr);
  }
  else if(expr.id() == ID_sva_sequence_consecutive_repetition) // x[*1:2]
  {
    auto &repetition = to_sva_sequence_consecutive_repetition_expr(expr);

    convert_sva(repetition.op());
    make_boolean(repetition.op());

    convert_expr(repetition.from());

    if(repetition.to().is_not_nil())
      convert_expr(repetition.to());

    expr.type() = bool_typet{};
    return std::move(expr);
  }
  else if(
    expr.id() == ID_sva_eventually || expr.id() == ID_sva_ranged_s_eventually ||
    expr.id() == ID_sva_s_always || expr.id() == ID_sva_ranged_always)
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

    convert_sva(expr.op2());
    make_boolean(expr.op2());
    expr.type() = bool_typet();

    return std::move(expr);
  }
  else if(expr.id() == ID_sva_if)
  {
    convert_expr(expr.op0());
    make_boolean(expr.op0());

    convert_sva(expr.op1());
    make_boolean(expr.op1());

    if(expr.op2().is_not_nil())
    {
      convert_sva(expr.op2());
      make_boolean(expr.op2());
    }

    return std::move(expr);
  }
  else
  {
    // not SVA
    return convert_expr_rec(std::move(expr));
  }
}

exprt verilog_typecheck_exprt::convert_sva_rec(exprt expr)
{
  switch(expr.operands().size())
  {
  case 1:
    return convert_unary_sva(to_unary_expr(expr));
  case 2:
    return convert_binary_sva(to_binary_expr(expr));
  case 3:
    return convert_ternary_sva(to_ternary_expr(expr));
  default:
    return convert_expr_rec(expr);
  }
}
