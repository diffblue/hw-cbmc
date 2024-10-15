/*******************************************************************\

Module: Property Normalization

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "normalize_property.h"

#include <util/arith_tools.h>
#include <util/mathematical_types.h>
#include <util/std_expr.h>

#include <verilog/sva_expr.h>

#include "nnf.h"
#include "temporal_expr.h"
#include "temporal_logic.h"
#include "trivial_sva.h"

exprt normalize_pre_sva_non_overlapped_implication(
  sva_non_overlapped_implication_exprt expr)
{
  // Same as a->always[1:1] b if lhs is not a sequence.
  if(!is_SVA_sequence(expr.lhs()))
  {
    auto one = natural_typet{}.one_expr();
    return or_exprt{
      not_exprt{expr.lhs()}, sva_ranged_always_exprt{one, one, expr.rhs()}};
  }
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
      // ##[0:$] φ --> s_eventually φ
      return sva_s_eventually_exprt{expr.op()};
    }
    else
    {
      // ##[i:$] φ --> always[i:i] s_eventually φ
      return sva_ranged_always_exprt{
        expr.from(), expr.from(), sva_s_eventually_exprt{expr.op()}};
    }
  }
  else
    return std::move(expr);
}

exprt normalize_property_rec(exprt expr)
{
  // pre-traversal
  if(expr.id() == ID_sva_non_overlapped_implication)
  {
    expr = normalize_pre_sva_non_overlapped_implication(
      to_sva_non_overlapped_implication_expr(expr));
  }
  else if(expr.id() == ID_sva_nexttime)
  {
    auto one = natural_typet{}.one_expr();
    expr = sva_ranged_always_exprt{one, one, to_sva_nexttime_expr(expr).op()};
  }
  else if(expr.id() == ID_sva_s_nexttime)
  {
    auto one = natural_typet{}.one_expr();
    expr = sva_s_always_exprt{one, one, to_sva_s_nexttime_expr(expr).op()};
  }
  else if(expr.id() == ID_sva_indexed_nexttime)
  {
    auto &nexttime_expr = to_sva_indexed_nexttime_expr(expr);
    expr = sva_ranged_always_exprt{
      nexttime_expr.index(), nexttime_expr.index(), nexttime_expr.op()};
  }
  else if(expr.id() == ID_sva_indexed_s_nexttime)
  {
    auto &nexttime_expr = to_sva_indexed_s_nexttime_expr(expr);
    expr = sva_s_always_exprt{
      nexttime_expr.index(), nexttime_expr.index(), nexttime_expr.op()};
  }
  else if(expr.id() == ID_sva_cycle_delay)
  {
    expr = normalize_pre_sva_cycle_delay(to_sva_cycle_delay_expr(expr));
  }
  else if(expr.id() == ID_sva_cycle_delay_plus)
  {
    expr = sva_s_nexttime_exprt{
      sva_s_eventually_exprt{to_sva_cycle_delay_plus_expr(expr).op()}};
  }
  else if(expr.id() == ID_sva_cycle_delay_star)
  {
    expr = sva_s_eventually_exprt{to_sva_cycle_delay_star_expr(expr).op()};
  }
  else if(expr.id() == ID_sva_strong)
  {
    expr = to_sva_strong_expr(expr).op();
  }
  else if(expr.id() == ID_sva_weak)
  {
    expr = to_sva_weak_expr(expr).op();
  }

  // normalize the operands
  for(auto &op : expr.operands())
    op = normalize_property_rec(op); // recursive call

  // post-traversal

  return expr;
}

exprt normalize_property(exprt expr)
{
  // top-level only
  if(expr.id() == ID_sva_cover)
    expr = G_exprt{not_exprt{to_sva_cover_expr(expr).op()}};

  expr = trivial_sva(expr);

  // now do recursion
  expr = normalize_property_rec(expr);

  // NNF
  expr = property_nnf(expr);

  return expr;
}
