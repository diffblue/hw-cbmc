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

constant_exprt verilog_event_typet::null_expr() const
{
  return encoding().all_zeros_expr();
}

void verilog_package_scope_typet::check(
  const typet &type,
  const validation_modet vm)
{
  PRECONDITION(type.id() == ID_verilog_package_scope);
  type_with_subtypest::check(type);
  DATA_CHECK(
    vm,
    to_type_with_subtypes(type).subtypes().size() == 2,
    "verilog_package_scope type must have two subtypes");
}
