/*******************************************************************\

Module: CTL

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "ctl.h"

#include "temporal_logic.h"

bool is_AGp(const exprt &expr)
{
  return expr.id() == ID_AG && !has_temporal_operator(to_AG_expr(expr).op());
}
