/*******************************************************************\

Module: Trivial SVA

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "trivial_sva.h"

#include <verilog/sva_expr.h>

#include "temporal_logic.h"

static std::optional<exprt> is_state_predicate(const exprt &expr)
{
  if(expr.id() == ID_sva_boolean)
    return to_sva_boolean_expr(expr).op();
  else
    return {};
}

exprt trivial_sva(exprt expr)
{
  // pre-traversal
  if(expr.id() == ID_sva_overlapped_implication)
  {
    // Same as regular implication if lhs and rhs are not sequences.
    auto &sva_implication = to_sva_overlapped_implication_expr(expr);

    auto lhs = is_state_predicate(sva_implication.lhs());
    auto rhs = is_state_predicate(sva_implication.rhs());

    if(lhs.has_value() && rhs.has_value())
      expr = sva_boolean_exprt{implies_exprt{*lhs, *rhs}, verilog_sva_property_typet{}};
  }
  else if(expr.id() == ID_sva_iff)
  {
    // same as boolean iff when both lhs/rhs are state predicates
    auto &sva_iff = to_sva_iff_expr(expr);

    auto lhs = is_state_predicate(sva_iff.lhs());
    auto rhs = is_state_predicate(sva_iff.rhs());

    if(lhs.has_value() && rhs.has_value())
      expr = sva_boolean_exprt{equal_exprt{*lhs, *rhs}, verilog_sva_property_typet{}};
  }
  else if(expr.id() == ID_sva_implies)
  {
    // same as boolean implication when both lhs/rhs are state predicates
    auto &sva_implies = to_sva_implies_expr(expr);

    auto lhs = is_state_predicate(sva_implies.lhs());
    auto rhs = is_state_predicate(sva_implies.rhs());

    if(lhs.has_value() && rhs.has_value())
      expr = sva_boolean_exprt{implies_exprt{*lhs, *rhs}, verilog_sva_property_typet{}};
  }
  else if(expr.id() == ID_sva_and)
  {
    auto &sva_and = to_sva_and_expr(expr);

    // can be sequence or property
    if(expr.type().id() == ID_verilog_sva_sequence)
    {
      // Same as a ∧ b if the expression is not a sequence.
      auto lhs = is_state_predicate(sva_and.lhs());
      auto rhs = is_state_predicate(sva_and.rhs());

      if(lhs.has_value() && rhs.has_value())
        expr = sva_boolean_exprt{and_exprt{*lhs, *rhs}, expr.type()};
    }
    else
    {
      expr = and_exprt{sva_and.lhs(), sva_and.rhs()};
    }
  }
  else if(expr.id() == ID_sva_or)
  {
    auto &sva_or = to_sva_or_expr(expr);

    // can be sequence or property
    if(expr.type().id() == ID_verilog_sva_sequence)
    {
      // Same as a ∨ b if the expression is not a sequence.
      auto lhs = is_state_predicate(sva_or.lhs());
      auto rhs = is_state_predicate(sva_or.rhs());

      if(lhs.has_value() && rhs.has_value())
        expr = sva_boolean_exprt{or_exprt{*lhs, *rhs}, expr.type()};
    }
    else
    {
      expr = or_exprt{sva_or.lhs(), sva_or.rhs()};
    }
  }
  else if(expr.id() == ID_sva_not)
  {
    // Same as boolean 'not' when applied to a state predicate.
    auto &op = to_sva_not_expr(expr).op();
    auto predicate = is_state_predicate(op);
    if(predicate.has_value())
      expr = sva_boolean_exprt{not_exprt{*predicate}, verilog_sva_property_typet{}};
  }
  else if(expr.id() == ID_sva_if)
  {
    // same as boolean 'if' when both cases are state predicates.
    auto &sva_if_expr = to_sva_if_expr(expr);
    auto false_case = sva_if_expr.false_case().is_nil()
                        ? true_exprt{}
                        : sva_if_expr.false_case();
    expr = if_exprt{sva_if_expr.cond(), sva_if_expr.true_case(), false_case};
  }
  else if(expr.id() == ID_sva_disable_iff)
  {
    auto &disable_iff_expr = to_sva_disable_iff_expr(expr);
    expr = or_exprt{disable_iff_expr.lhs(), disable_iff_expr.rhs()};
  }
  else if(expr.id() == ID_sva_accept_on || expr.id() == ID_sva_sync_accept_on)
  {
    auto &sva_abort_expr = to_sva_abort_expr(expr);
    expr = or_exprt{sva_abort_expr.condition(), sva_abort_expr.property()};
  }
  else if(expr.id() == ID_sva_reject_on || expr.id() == ID_sva_sync_reject_on)
  {
    auto &sva_abort_expr = to_sva_abort_expr(expr);
    expr = and_exprt{
      not_exprt{sva_abort_expr.condition()}, sva_abort_expr.property()};
  }
  else if(expr.id() == ID_sva_case)
  {
    expr = to_sva_case_expr(expr).lower();
  }

  // rewrite the operands, recursively
  for(auto &op : expr.operands())
    op = trivial_sva(op);

  // post-traversal
  if(
    expr.id() == ID_sva_weak || expr.id() == ID_sva_strong ||
    expr.id() == ID_sva_implicit_weak || expr.id() == ID_sva_implicit_strong)
  {
    // We simplify sequences to boolean expressions, and hence can drop
    // the sva_sequence_property converter
    auto &sequence = to_sva_sequence_property_expr_base(expr).sequence();
    auto pred_opt = is_state_predicate(sequence);
    if(pred_opt.has_value())
      return *pred_opt;
  }

  return expr;
}
