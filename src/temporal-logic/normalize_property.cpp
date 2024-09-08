/*******************************************************************\

Module: Property Normalization

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "normalize_property.h"

#include <util/arith_tools.h>
#include <util/std_expr.h>

#include <verilog/sva_expr.h>

#include "temporal_expr.h"
#include "temporal_logic.h"

exprt normalize_pre_not(not_exprt expr)
{
  const auto &op = expr.op();

  if(op.id() == ID_and)
  {
    auto operands = op.operands();
    for(auto &op : operands)
      op = not_exprt{op};
    return or_exprt{std::move(operands)};
  }
  else if(op.id() == ID_or)
  {
    auto operands = op.operands();
    for(auto &op : operands)
      op = not_exprt{op};
    return and_exprt{std::move(operands)};
  }
  else if(op.id() == ID_not)
  {
    return to_not_expr(op).op();
  }
  else if(op.id() == ID_G)
  {
    // ¬Gφ --> F¬φ
    return F_exprt{not_exprt{to_G_expr(op).op()}};
  }
  else if(op.id() == ID_F)
  {
    // ¬Fφ --> G¬φ
    return G_exprt{not_exprt{to_F_expr(op).op()}};
  }
  else if(op.id() == ID_X)
  {
    // ¬Xφ --> X¬φ
    return X_exprt{not_exprt{to_X_expr(op).op()}};
  }
  else if(op.id() == ID_sva_always)
  {
    // ¬ sva_always φ --> sva_s_eventually ¬φ
    return sva_s_eventually_exprt{not_exprt{to_sva_always_expr(op).op()}};
  }
  else if(op.id() == ID_sva_s_eventually)
  {
    // ¬ sva_s_eventually φ --> sva_always ¬φ
    return sva_always_exprt{not_exprt{to_sva_eventually_expr(op).op()}};
  }

  return std::move(expr);
}

exprt normalize_pre_implies(implies_exprt expr)
{
  return or_exprt{not_exprt{expr.lhs()}, expr.rhs()};
}

exprt normalize_pre_sva_overlapped_implication(
  sva_overlapped_implication_exprt expr)
{
  // Same as regular implication if lhs and rhs are not
  // sequences.
  if(!is_SVA_sequence(expr.lhs()) && !is_SVA_sequence(expr.rhs()))
    return or_exprt{not_exprt{expr.lhs()}, expr.rhs()};
  else
    return std::move(expr);
}

exprt normalize_pre_sva_non_overlapped_implication(
  sva_non_overlapped_implication_exprt expr)
{
  // Same as a->Xb if lhs and rhs are not sequences.
  if(!is_SVA_sequence(expr.lhs()) && !is_SVA_sequence(expr.rhs()))
    return or_exprt{not_exprt{expr.lhs()}, X_exprt{expr.rhs()}};
  else
    return std::move(expr);
}

exprt normalize_pre_sva_not(sva_not_exprt expr)
{
  // Same as regular 'not'. These do not apply to sequences.
  return not_exprt{expr.op()};
}

exprt normalize_pre_sva_and(sva_and_exprt expr)
{
  // Same as a ∧ b if lhs and rhs are not sequences.
  if(!is_SVA_sequence(expr.lhs()) && !is_SVA_sequence(expr.rhs()))
    return and_exprt{expr.lhs(), expr.rhs()};
  else
    return std::move(expr);
}

exprt normalize_pre_sva_or(sva_or_exprt expr)
{
  // Same as a ∧ b if lhs or rhs are not sequences.
  if(!is_SVA_sequence(expr.lhs()) && !is_SVA_sequence(expr.rhs()))
    return or_exprt{expr.lhs(), expr.rhs()};
  else
    return std::move(expr);
}

exprt normalize_pre_sva_cycle_delay(sva_cycle_delay_exprt expr)
{
  if(expr.is_unbounded())
  {
    if(
      expr.from().is_constant() &&
      numeric_cast_v<mp_integer>(to_constant_expr(expr.from())) == 0)
    {
      // ##[0:$] φ --> F φ
      return F_exprt{expr.op()};
    }
    else
    {
      // ##[i:$] φ --> ##i F φ
      return sva_cycle_delay_exprt{expr.from(), F_exprt{expr.op()}};
    }
  }
  else
    return std::move(expr);
}

exprt normalize_property(exprt expr)
{
  // pre-traversal
  if(expr.id() == ID_not)
    expr = normalize_pre_not(to_not_expr(expr));
  else if(expr.id() == ID_implies)
    expr = normalize_pre_implies(to_implies_expr(expr));
  else if(expr.id() == ID_sva_cover)
    expr = G_exprt{not_exprt{to_sva_cover_expr(expr).op()}};
  else if(expr.id() == ID_sva_overlapped_implication)
    expr = normalize_pre_sva_overlapped_implication(
      to_sva_overlapped_implication_expr(expr));
  else if(expr.id() == ID_sva_non_overlapped_implication)
    expr = normalize_pre_sva_non_overlapped_implication(
      to_sva_non_overlapped_implication_expr(expr));
  else if(expr.id() == ID_sva_and)
    expr = normalize_pre_sva_and(to_sva_and_expr(expr));
  else if(expr.id() == ID_sva_not)
    expr = normalize_pre_sva_not(to_sva_not_expr(expr));
  else if(expr.id() == ID_sva_or)
    expr = normalize_pre_sva_or(to_sva_or_expr(expr));
  else if(expr.id() == ID_sva_nexttime)
  {
    auto &nexttime_expr = to_sva_nexttime_expr(expr);
    if(nexttime_expr.is_indexed())
      expr = sva_ranged_always_exprt{
        nexttime_expr.index(), nexttime_expr.index(), nexttime_expr.op()};
    else
      expr = X_exprt{nexttime_expr.op()};
  }
  else if(expr.id() == ID_sva_s_nexttime)
  {
    auto &nexttime_expr = to_sva_s_nexttime_expr(expr);
    if(nexttime_expr.is_indexed())
      expr = sva_s_always_exprt{
        nexttime_expr.index(), nexttime_expr.index(), nexttime_expr.op()};
    else
      expr = X_exprt{to_sva_s_nexttime_expr(expr).op()};
  }
  else if(expr.id() == ID_sva_cycle_delay)
    expr = normalize_pre_sva_cycle_delay(to_sva_cycle_delay_expr(expr));
  else if(expr.id() == ID_sva_cycle_delay_plus)
    expr = F_exprt{X_exprt{to_sva_cycle_delay_plus_expr(expr).op()}};
  else if(expr.id() == ID_sva_cycle_delay_star)
    expr = X_exprt{to_sva_cycle_delay_star_expr(expr).op()};
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
  else if(expr.id() == ID_sva_strong)
  {
    expr = to_sva_strong_expr(expr).op();
  }
  else if(expr.id() == ID_sva_weak)
  {
    expr = to_sva_weak_expr(expr).op();
  }
  else if(expr.id() == ID_sva_case)
  {
    expr = to_sva_case_expr(expr).lowering();
  }

  // normalize the operands
  for(auto &op : expr.operands())
    op = normalize_property(op);

  // post-traversal

  return expr;
}
