/*******************************************************************\

Module: Property Normalization

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "normalize_property.h"

#include <util/arith_tools.h>
#include <util/mathematical_types.h>
#include <util/std_expr.h>

#include <verilog/sva_expr.h>

#include "ltl.h"
#include "temporal_expr.h"
#include "temporal_logic.h"
#include "trivial_sva.h"

exprt normalize_pre_sva_non_overlapped_implication(
  sva_non_overlapped_implication_exprt expr)
{
  // a|=>b is the same as a->always[1:1] b if lhs is not a proper sequence.
  if(expr.lhs().id() == ID_sva_boolean)
  {
    const auto &lhs_cond = to_sva_boolean_expr(expr.lhs()).op();
    auto one = natural_typet{}.one_expr();
    auto ranged_always = sva_ranged_always_exprt{one, one, expr.rhs()};
    ranged_always.type() = bool_typet{};
    return or_exprt{not_exprt{lhs_cond}, ranged_always};
  }
  else
    return std::move(expr);
}

exprt normalize_pre_sva_overlapped_implication(
  sva_overlapped_implication_exprt expr)
{
  // a|->b is the same as a->b if lhs is not a proper sequence.
  if(expr.lhs().id() == ID_sva_boolean)
  {
    const auto &lhs_cond = to_sva_boolean_expr(expr.lhs()).op();
    return implies_exprt{lhs_cond, expr.rhs()};
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
  else if(expr.id() == ID_sva_overlapped_implication)
  {
    expr = normalize_pre_sva_overlapped_implication(
      to_sva_overlapped_implication_expr(expr));
  }
  else if(expr.id() == ID_sva_nexttime)
  {
    auto one = natural_typet{}.one_expr();
    expr = sva_ranged_always_exprt{
      one, one, to_sva_nexttime_expr(expr).op(), bool_typet{}};
  }
  else if(expr.id() == ID_sva_s_nexttime)
  {
    auto one = natural_typet{}.one_expr();
    expr = sva_s_always_exprt{
      one, one, to_sva_s_nexttime_expr(expr).op(), bool_typet{}};
  }
  else if(expr.id() == ID_sva_indexed_nexttime)
  {
    auto &nexttime_expr = to_sva_indexed_nexttime_expr(expr);
    expr = sva_ranged_always_exprt{
      nexttime_expr.index(),
      nexttime_expr.index(),
      nexttime_expr.op(),
      bool_typet{}};
  }
  else if(expr.id() == ID_sva_indexed_s_nexttime)
  {
    auto &nexttime_expr = to_sva_indexed_s_nexttime_expr(expr);
    expr = sva_s_always_exprt{
      nexttime_expr.index(),
      nexttime_expr.index(),
      nexttime_expr.op(),
      bool_typet{}};
  }

  // normalize the operands
  for(auto &op : expr.operands())
    op = normalize_property_rec(op); // recursive call

  // post-traversal
  if(expr.id() == ID_R)
  {
    if(to_R_expr(expr).lhs().is_false())
    {
      // false R ψ ≡ G ψ
      expr = G_exprt{to_R_expr(expr).rhs()};
    }
  }

  return expr;
}

exprt normalize_property(exprt expr)
{
  // top-level only
  if(expr.id() == ID_sva_cover)
    expr = sva_always_exprt{sva_not_exprt{to_sva_cover_expr(expr).op()}};

  expr = trivial_sva(expr);

  // now do recursion
  expr = normalize_property_rec(expr);

  return expr;
}
