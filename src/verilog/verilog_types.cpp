/*******************************************************************\

Module: Verilog Types

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_types.h"

#include <util/arith_tools.h>
#include <util/mathematical_types.h>
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

verilog_array_typet::verilog_array_typet(
  irep_idt verilog_type,
  typet element_type,
  mp_integer size,
  mp_integer offset,
  bool increasing)
  : array_typet{std::move(element_type), from_integer(size, integer_typet{})}
{
  set(ID_C_verilog_type, verilog_type);
  set(ID_offset, integer2string(offset));
  set(ID_C_increasing, increasing);
}

mp_integer verilog_array_typet::size_int() const
{
  auto size_opt = numeric_cast<mp_integer>(size());
  PRECONDITION(size_opt.has_value());
  return size_opt.value();
}

mp_integer verilog_array_typet::offset() const
{
  auto &offset_irep = static_cast<const exprt &>(find(ID_offset));
  DATA_INVARIANT(offset_irep.is_not_nil(), "array must have offset");
  return string2integer(offset_irep.id_string());
}

typet verilog_array_typet::index_type() const
{
  return unsignedbv_typet{
    numeric_cast_v<std::size_t>(address_bits((size_int() + offset())))};
}
