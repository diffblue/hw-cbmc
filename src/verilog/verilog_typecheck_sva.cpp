/*******************************************************************\

Module: Typechecking for SVA

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/mathematical_types.h>

#include <temporal-logic/temporal_logic.h>

#include "sva_expr.h"
#include "verilog_typecheck_expr.h"
#include "verilog_types.h"

void verilog_typecheck_exprt::require_sva_sequence(exprt &expr)
{
  auto &type = expr.type();

  if(type.id() == ID_verilog_sva_sequence)
  {
    // good as is
  }
  else if(
    type.id() == ID_bool || type.id() == ID_unsignedbv ||
    type.id() == ID_signedbv || type.id() == ID_verilog_unsignedbv ||
    type.id() == ID_verilog_signedbv)
  {
    if(has_temporal_operator(expr))
    {
      throw errort().with_location(expr.source_location())
        << "sequence required, but got property";
    }
    else
    {
      // state formula, can convert to sequence
      make_boolean(expr);
      expr = sva_boolean_exprt{std::move(expr), verilog_sva_sequence_typet{}};
    }
  }
  else
  {
    throw errort().with_location(expr.source_location())
      << "sequence required, but got " << to_string(type);
  }
}

void verilog_typecheck_exprt::require_sva_property(exprt &expr)
{
  auto &type = expr.type();

  if(type.id() == ID_verilog_sva_sequence)
  {
    // 1800 2017 16.12.2 Sequence property
    // These yield an implicit weak(...) or strong(...), but we
    // only know which one once the sequence is used in an assert/assume
    // or cover.
    expr = sva_sequence_property_exprt{std::move(expr)};
  }
  else if(
    type.id() == ID_bool || type.id() == ID_unsignedbv ||
    type.id() == ID_signedbv || type.id() == ID_verilog_unsignedbv ||
    type.id() == ID_verilog_signedbv)
  {
    // property or state formula, can cast
    make_boolean(expr);
  }
  else
  {
    throw errort().with_location(expr.source_location())
      << "sequence required, but got " << to_string(type);
  }
}

exprt verilog_typecheck_exprt::convert_unary_sva(unary_exprt expr)
{
  if(
    expr.id() == ID_sva_not || expr.id() == ID_sva_always ||
    expr.id() == ID_sva_s_eventually || expr.id() == ID_sva_nexttime ||
    expr.id() == ID_sva_s_nexttime)
  {
    convert_sva(expr.op());
    require_sva_property(expr.op());
    expr.type() = bool_typet{}; // always boolean, never x
    return std::move(expr);
  }
  else if(expr.id() == ID_sva_weak || expr.id() == ID_sva_strong)
  {
    convert_sva(expr.op());
    require_sva_sequence(expr.op());
    expr.type() = bool_typet{};
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
  if(expr.id() == ID_sva_and || expr.id() == ID_sva_or)
  {
    for(auto &op : expr.operands())
      convert_sva(op);

    // These yield sequences when both operands are sequences, and
    // properties otherwise.
    if(
      (expr.lhs().type().id() == ID_verilog_sva_sequence ||
       !has_temporal_operator(expr.lhs())) &&
      (expr.rhs().type().id() == ID_verilog_sva_sequence ||
       !has_temporal_operator(expr.rhs())))
    {
      expr.type() = verilog_sva_sequence_typet{};
      require_sva_sequence(expr.lhs());
      require_sva_sequence(expr.rhs());
    }
    else
    {
      require_sva_property(expr.lhs());
      require_sva_property(expr.rhs());
      // always boolean, never x
      expr.type() = bool_typet{};
    }

    return std::move(expr);
  }
  else if(expr.id() == ID_sva_implies || expr.id() == ID_sva_iff)
  {
    convert_sva(expr.lhs());
    convert_sva(expr.rhs());

    require_sva_property(expr.lhs());
    require_sva_property(expr.rhs());

    // always boolean, never x
    expr.type() = bool_typet{};

    return std::move(expr);
  }
  else if(
    expr.id() == ID_sva_disable_iff || expr.id() == ID_sva_accept_on ||
    expr.id() == ID_sva_reject_on || expr.id() == ID_sva_sync_accept_on ||
    expr.id() == ID_sva_sync_reject_on)
  {
    // The condition of these is special: They are not sampled,
    // but evaluated directly (1800-2017 16.6).
    convert_expr(to_sva_abort_expr(expr).condition());
    make_boolean(to_sva_abort_expr(expr).condition());

    convert_sva(to_sva_abort_expr(expr).property());
    require_sva_property(to_sva_abort_expr(expr).property());
    expr.type() = bool_typet{};

    return std::move(expr);
  }
  else if(
    expr.id() == ID_sva_cycle_delay_plus || // ##[+]
    expr.id() == ID_sva_cycle_delay_star)   // ##[*]
  {
    // These take sequences as argument. The LHS is optional.
    if(expr.lhs().is_not_nil())
    {
      convert_sva(expr.lhs());
      require_sva_sequence(expr.lhs());
    }

    convert_sva(expr.rhs());
    require_sva_sequence(expr.rhs());

    expr.type() = verilog_sva_sequence_typet{};

    return std::move(expr);
  }
  else if(expr.id() == ID_sva_indexed_nexttime)
  {
    convert_expr(to_sva_indexed_nexttime_expr(expr).index());

    auto &op = to_sva_indexed_nexttime_expr(expr).op();
    convert_sva(op);
    require_sva_property(op);
    expr.type() = bool_typet{};

    return std::move(expr);
  }
  else if(expr.id() == ID_sva_indexed_s_nexttime)
  {
    convert_expr(to_sva_indexed_s_nexttime_expr(expr).index());

    auto &op = to_sva_indexed_s_nexttime_expr(expr).op();
    convert_sva(op);
    require_sva_property(op);
    expr.type() = bool_typet{};

    return std::move(expr);
  }
  else if(
    expr.id() == ID_sva_overlapped_implication ||
    expr.id() == ID_sva_non_overlapped_implication ||
    expr.id() == ID_sva_overlapped_followed_by ||
    expr.id() == ID_sva_nonoverlapped_followed_by)
  {
    // These all take a sequence on the LHS, and a property on the RHS.
    // The grammar allows properties on the LHS to implement and/or over
    // sequences. Check here that the LHS is a sequence.
    convert_sva(expr.lhs());
    require_sva_sequence(expr.lhs());

    convert_sva(expr.rhs());
    require_sva_property(expr.rhs());

    expr.type() = bool_typet{};
    return std::move(expr);
  }
  else if(
    expr.id() == ID_sva_until || expr.id() == ID_sva_s_until ||
    expr.id() == ID_sva_until_with || expr.id() == ID_sva_s_until_with)
  {
    convert_sva(expr.lhs());
    require_sva_property(expr.lhs());

    convert_sva(expr.rhs());
    require_sva_property(expr.rhs());

    expr.type() = bool_typet{};

    return std::move(expr);
  }
  else if(
    expr.id() == ID_sva_sequence_intersect ||
    expr.id() == ID_sva_sequence_within)
  {
    // This requires a sequence on the LHS.
    // The grammar allows properties on the LHS to implement and/or over
    // sequences. Check here that the LHS is a sequence.
    convert_sva(expr.lhs());
    require_sva_sequence(expr.lhs());

    convert_sva(expr.rhs());
    require_sva_sequence(expr.rhs());

    expr.type() = verilog_sva_sequence_typet{};

    return std::move(expr);
  }
  else if(expr.id() == ID_sva_sequence_throughout)
  {
    // The LHS is a Boolean condition, the RHS a sequence.
    convert_expr(expr.lhs());
    make_boolean(expr.lhs());

    convert_sva(expr.rhs());
    require_sva_sequence(expr.rhs());

    expr.type() = verilog_sva_sequence_typet{};

    return std::move(expr);
  }
  else if(expr.id() == ID_sva_sequence_first_match)
  {
    auto &first_match_expr = to_sva_sequence_first_match_expr(expr);

    convert_sva(first_match_expr.sequence());
    require_sva_sequence(first_match_expr.sequence());

    if(first_match_expr.rhs().is_not_nil())
      convert_expr(first_match_expr.rhs());

    expr.type() = verilog_sva_sequence_typet{};

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
      require_sva_property(case_item.result());
    }

    expr.type() = bool_typet{};
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
  if(expr.id() == ID_sva_sequence_repetition_star) // x[*1:2]
  {
    // This expression takes a sequence as argument.
    // The grammar allows properties to implement and/or over
    // sequences. Check here that the argument is a sequence.
    convert_sva(expr.op0());
    require_sva_sequence(expr.op0());

    if(expr.op1().is_not_nil())
      convert_expr(expr.op1());

    if(expr.op2().is_not_nil())
      convert_expr(expr.op2());

    expr.type() = verilog_sva_sequence_typet{};
    return std::move(expr);
  }
  else if(expr.id() == ID_sva_sequence_repetition_plus) // x[+]
  {
    // These take a sequence as argument.
    // The grammar allows properties to implement and/or over
    // sequences. Check here that the argument is a sequence.
    // op1() and op2() are nil.
    // The forms op[+x] and op[+x:y] do not exist.
    convert_sva(expr.op0());
    require_sva_sequence(expr.op0());
    expr.type() = verilog_sva_sequence_typet{};
    return std::move(expr);
  }
  else if(
    expr.id() == ID_sva_sequence_non_consecutive_repetition ||
    expr.id() == ID_sva_sequence_goto_repetition)
  {
    // These take a Boolean as argument.
    convert_expr(expr.op0());
    make_boolean(expr.op0());

    convert_expr(expr.op1());

    mp_integer n = elaborate_constant_integer_expression(expr.op1());
    if(n < 0)
      throw errort().with_location(expr.op1().source_location())
        << "number of repetitions must not be negative";

    expr.op1() = from_integer(n, integer_typet{});

    if(expr.op2().is_not_nil())
      convert_expr(expr.op2());

    expr.type() = verilog_sva_sequence_typet{};

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
    require_sva_property(expr.op2());
    expr.type() = bool_typet{};

    return std::move(expr);
  }
  else if(expr.id() == ID_sva_if)
  {
    convert_expr(expr.op0());
    make_boolean(expr.op0());

    convert_sva(expr.op1());
    require_sva_property(expr.op1());

    if(expr.op2().is_not_nil())
    {
      convert_sva(expr.op2());
      require_sva_property(expr.op2());
    }

    // These are always property expressions
    expr.type() = bool_typet{};

    return std::move(expr);
  }
  else
  {
    // not SVA
    return convert_expr_rec(std::move(expr));
  }
}

exprt verilog_typecheck_exprt::convert_other_sva(exprt expr)
{
  if(expr.id() == ID_sva_cycle_delay) // ##[1:2] something
  {
    expr.type() = verilog_sva_sequence_typet{};

    DATA_INVARIANT(
      expr.operands().size() == 4, "sva_cycle_delay has four operands");

    // lhs
    if(expr.operands()[0].is_not_nil())
    {
      convert_sva(expr.operands()[0]);
      require_sva_sequence(expr.operands()[0]);
    }

    // from
    convert_expr(expr.operands()[1]);
    elaborate_constant_expression_check(expr.operands()[1]);

    // to
    if(expr.operands()[2].is_not_nil())
    {
      convert_expr(expr.operands()[2]);
      elaborate_constant_expression_check(expr.operands()[2]);
    }

    // rhs
    convert_sva(expr.operands()[3]);
    require_sva_sequence(expr.operands()[3]);

    return expr;
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
    return convert_other_sva(expr);
  }
}

// 1800-2017 16.12.2 Sequence property
// Sequences are by default _weak_ when used in assert property
// or assume property, and are _strong_ when used in cover property.
// This flips when below the SVA not operator.
void verilog_typecheck_exprt::set_default_sequence_semantics(
  exprt &expr,
  sva_sequence_semanticst semantics)
{
  if(expr.id() == ID_sva_sequence_property)
  {
    // apply
    if(semantics == sva_sequence_semanticst::WEAK)
      expr.id(ID_sva_implicit_weak);
    else
      expr.id(ID_sva_implicit_strong);
  }
  else if(expr.id() == ID_sva_not)
  {
    // flip
    semantics = semantics == sva_sequence_semanticst::WEAK
                  ? sva_sequence_semanticst::STRONG
                  : sva_sequence_semanticst::WEAK;

    set_default_sequence_semantics(to_sva_not_expr(expr).op(), semantics);
  }
  else
  {
    for(auto &op : expr.operands())
      set_default_sequence_semantics(op, semantics);
  }
}
