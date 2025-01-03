/*******************************************************************\

Module: Verilog Types

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_types.h"

#include <util/std_expr.h>

constant_exprt verilog_chandle_typet::null_expr() const
{
  return encoding().all_zeros_expr();
}
