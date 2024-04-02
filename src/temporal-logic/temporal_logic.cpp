/*******************************************************************\

Module: Temporal Logic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "temporal_logic.h"

#include <util/expr_iterator.h>

bool is_temporal_operator(const exprt &expr)
{
  return expr.id() == ID_AG || expr.id() == ID_EG || expr.id() == ID_AF ||
         expr.id() == ID_EF || expr.id() == ID_AX || expr.id() == ID_EX ||
         expr.id() == ID_A || expr.id() == ID_E || expr.id() == ID_U ||
         expr.id() == ID_R || expr.id() == ID_G || expr.id() == ID_F ||
         expr.id() == ID_X || expr.id() == ID_sva_always ||
         expr.id() == ID_sva_always || expr.id() == ID_sva_ranged_always ||
         expr.id() == ID_sva_nexttime || expr.id() == ID_sva_s_nexttime ||
         expr.id() == ID_sva_until || expr.id() == ID_sva_s_until ||
         expr.id() == ID_sva_until_with || expr.id() == ID_sva_s_until_with ||
         expr.id() == ID_sva_eventually || expr.id() == ID_sva_s_eventually ||
         expr.id() == ID_sva_cycle_delay;
}

bool has_temporal_operator(const exprt &expr)
{
  for(auto subexpr_it = expr.depth_cbegin(), subexpr_end = expr.depth_cend();
      subexpr_it != subexpr_end;
      subexpr_it++)
  {
    if(is_temporal_operator(*subexpr_it))
      return true;
  }

  return false;
}
