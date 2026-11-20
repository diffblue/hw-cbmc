/*******************************************************************\

Module: Verilog Constants

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_constant.h"

#include <util/expr.h>

bool is_verilog_constant(const exprt &expr)
{
  // $ counts as a constant
  if(expr.is_constant() || expr.id() == ID_infinity)
    return true;

  if(expr.id() == ID_struct || expr.id() == ID_array || expr.id() == ID_union)
  {
    for(auto &op : expr.operands())
      if(!is_verilog_constant(op))
        return false;
    return true;
  }

  return false;
}
