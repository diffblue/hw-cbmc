/*******************************************************************\

Module: Unwinding the Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "obligations.h"

#include <util/std_expr.h>

std::pair<mp_integer, exprt> obligationst::conjunction() const
{
  mp_integer max = 0;
  exprt::operandst conjuncts;
  for(auto &obligation : map)
  {
    max = std::max(obligation.first, max);
    for(auto &cond : obligation.second)
      conjuncts.push_back(cond);
  }
  return {max, ::conjunction(conjuncts)};
}
