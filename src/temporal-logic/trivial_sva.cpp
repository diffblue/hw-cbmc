/*******************************************************************\

Module: Trivial SVA

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "trivial_sva.h"

#include <verilog/sva_expr.h>

#include "temporal_logic.h"

static std::optional<exprt> is_state_formula(const exprt &expr)
{
  if(expr.id() == ID_typecast && expr.type().id() == ID_verilog_sva_sequence)
    return to_typecast_expr(expr).op();
  else if(expr.type().id() == ID_bool)
    return expr;
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

    auto lhs = is_state_formula(sva_implication.lhs());
    auto rhs = is_state_formula(sva_implication.rhs());

    if(lhs.has_value() && rhs.has_value())
      expr = implies_exprt{*lhs, *rhs};
  }
  else if(expr.id() == ID_sva_iff)
  {
    auto &sva_iff = to_sva_iff_expr(expr);
    expr = equal_exprt{sva_iff.lhs(), sva_iff.rhs()};
  }
  else if(expr.id() == ID_sva_implies)
  {
    auto &sva_implies = to_sva_implies_expr(expr);
    expr = implies_exprt{sva_implies.lhs(), sva_implies.rhs()};
  }
  else if(expr.id() == ID_sva_and)
  {
    auto &sva_and = to_sva_and_expr(expr);

    // Same as a ∧ b if the expression is not a sequence.
    auto lhs = is_state_formula(sva_and.lhs());
    auto rhs = is_state_formula(sva_and.rhs());

    if(lhs.has_value() && rhs.has_value())
      expr = and_exprt{*lhs, *rhs};
  }
  else if(expr.id() == ID_sva_or)
  {
    auto &sva_or = to_sva_or_expr(expr);

    // Same as a ∨ b if the expression is not a sequence.
    auto lhs = is_state_formula(sva_or.lhs());
    auto rhs = is_state_formula(sva_or.rhs());

    if(lhs.has_value() && rhs.has_value())
      expr = or_exprt{*lhs, *rhs};
  }
  else if(expr.id() == ID_sva_not)
  {
    // Same as regular 'not'. These do not apply to sequences.
    expr = not_exprt{to_sva_not_expr(expr).op()};
  }
  else if(expr.id() == ID_sva_if)
  {
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
    expr = to_sva_case_expr(expr).lowering();
  }

  // rewrite the operands, recursively
  for(auto &op : expr.operands())
    op = trivial_sva(op);

  // post-traversal
  if(expr.id() == ID_typecast)
  {
    // We typecast sequences to bool, and hence can drop
    // casts from bool to bool
    auto &op = to_typecast_expr(expr).op();
    if(expr.type().id() == ID_bool && op.type().id() == ID_bool)
      return op;
  }

  return expr;
}
