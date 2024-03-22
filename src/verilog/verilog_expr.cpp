/*******************************************************************\

Module: Verilog Expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_expr.h"

#include <util/prefix.h>

typet verilog_declaratort::merged_type(const typet &declaration_type) const
{
  typet result = type();
  typet *p = &result;

  while(p->id() == ID_verilog_unpacked_array)
    p = &to_type_with_subtype(*p).subtype();

  DATA_INVARIANT(p->is_nil(), "merged_type only works on unpacked arrays");
  *p = declaration_type;

  return result;
}

bool function_call_exprt::is_system_function_call() const
{
  return function().id() == ID_symbol &&
         has_prefix(
           id2string(to_symbol_expr(function()).get_identifier()), "$");
}
