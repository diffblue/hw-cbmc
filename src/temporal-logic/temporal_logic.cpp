/*******************************************************************\

Module: Temporal Logic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "temporal_logic.h"

#include <util/expr_iterator.h>

bool has_temporal_operator(const exprt &expr)
{
  for(auto subexpr_it = expr.depth_cbegin(), subexpr_end = expr.depth_cend();
      subexpr_it != subexpr_end;
      subexpr_it++)
  {
    // clang-format off
    if(
      subexpr_it->id() == ID_AG || subexpr_it->id() == ID_EG ||
      subexpr_it->id() == ID_AF || subexpr_it->id() == ID_EF ||
      subexpr_it->id() == ID_AX || subexpr_it->id() == ID_EX ||
      subexpr_it->id() == ID_A || subexpr_it->id() == ID_E ||
      subexpr_it->id() == ID_U || subexpr_it->id() == ID_R ||
      subexpr_it->id() == ID_G || subexpr_it->id() == ID_F ||
      subexpr_it->id() == ID_X ||
      subexpr_it->id() == ID_sva_always || subexpr_it->id() == ID_sva_always ||
      subexpr_it->id() == ID_sva_nexttime || subexpr_it->id() == ID_sva_s_nexttime ||
      subexpr_it->id() == ID_sva_until || subexpr_it->id() == ID_sva_s_until ||
      subexpr_it->id() == ID_sva_until_with || subexpr_it->id() == ID_sva_s_until_with ||
      subexpr_it->id() == ID_sva_eventually ||
      subexpr_it->id() == ID_sva_s_eventually)
    {
      return true;
    }
    // clang-format on
  }

  return false;
}
