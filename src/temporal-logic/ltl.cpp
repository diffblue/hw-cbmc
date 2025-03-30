/*******************************************************************\

Module: LTL

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "ltl.h"

#include "temporal_logic.h"

bool is_Gp(const exprt &expr)
{
  return expr.id() == ID_G && !has_temporal_operator(to_G_expr(expr).op());
}

bool is_GFp(const exprt &expr)
{
  return expr.id() == ID_G && to_G_expr(expr).op().id() == ID_F &&
         !has_temporal_operator(to_F_expr(to_G_expr(expr).op()).op());
}
