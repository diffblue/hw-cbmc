/*******************************************************************\

Module: Property Normalization

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "normalize_property.h"

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

  return std::move(expr);
}

exprt normalize_pre_implies(implies_exprt expr)
{
  return or_exprt{not_exprt{expr.lhs()}, expr.rhs()};
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

  // normalize the operands
  for(auto &op : expr.operands())
    op = normalize_property(op);

  // post-traversal

  return expr;
}
