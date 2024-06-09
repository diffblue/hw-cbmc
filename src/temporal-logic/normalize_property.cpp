/*******************************************************************\

Module: Property Normalization

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "normalize_property.h"

#include <util/arith_tools.h>
#include <util/std_expr.h>

#include <verilog/sva_expr.h>

#include "temporal_expr.h"

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

  return std::move(expr);
}

exprt normalize_pre_implies(implies_exprt expr)
{
  return or_exprt{not_exprt{expr.lhs()}, expr.rhs()};
}

exprt normalize_pre_sva_overlapped_implication(
  sva_overlapped_implication_exprt expr)
{
  // same as regular implication
  return or_exprt{not_exprt{expr.lhs()}, expr.rhs()};
}

exprt normalize_pre_sva_non_overlapped_implication(
  sva_non_overlapped_implication_exprt expr)
{
  // same as a->Xb
  return or_exprt{not_exprt{expr.lhs()}, X_exprt{expr.rhs()}};
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
  else if(expr.id() == ID_sva_nexttime)
  {
    if(!to_sva_nexttime_expr(expr).is_indexed())
      expr = X_exprt{to_sva_nexttime_expr(expr).op()};
  }
  else if(expr.id() == ID_sva_s_nexttime)
  {
    if(!to_sva_s_nexttime_expr(expr).is_indexed())
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

  // normalize the operands
  for(auto &op : expr.operands())
    op = normalize_property(op);

  // post-traversal

  return expr;
}
