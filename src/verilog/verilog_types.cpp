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

constant_exprt verilog_unsignedbv_typet::all_x_expr() const
{
  return constant_exprt{std::string(get_width(), 'x'), *this};
}

constant_exprt verilog_unsignedbv_typet::all_z_expr() const
{
  return constant_exprt{std::string(get_width(), 'z'), *this};
}

typet make_two_valued(typet src)
{
  if(src.id() == ID_verilog_unsignedbv)
  {
    // Is it [0:0]? If so, make it 'bool'
    if(
      to_verilog_unsignedbv_type(src).width() == 1 &&
      src.get(ID_C_offset) == irep_idt{})
    {
      auto result = bool_typet{}.with_source_location(src.source_location());
      irep_idt verilog_type = src.get(ID_C_verilog_type);
      if(verilog_type != irep_idt{})
        result.set(ID_C_verilog_type, verilog_type);
      return result;
    }
    else
    {
      // replace id, preserve width and location, if any
      src.id(ID_unsignedbv);
      return src;
    }
  }
  else if(src.id() == ID_verilog_signedbv)
  {
    // replace id, preserve width and location, if any
    src.id(ID_signedbv);
    return src;
  }
  else if(src.id() == ID_unsignedbv)
  {
    // Is it [0:0]? If so, make it 'bool'
    if(
      to_unsignedbv_type(src).width() == 1 &&
      src.get(ID_C_offset) == irep_idt{})
    {
      auto result = bool_typet{}.with_source_location(src.source_location());
      irep_idt verilog_type = src.get(ID_C_verilog_type);
      if(verilog_type != irep_idt{})
        result.set(ID_C_verilog_type, verilog_type);
      return result;
    }
    else
    {
      // leave as is
      return src;
    }
  }
  else if(src.id() == ID_array)
  {
    auto &array_type = to_array_type(src);
    array_type.element_type() = make_two_valued(array_type.element_type());
    return src;
  }
  else if(src.id() == ID_struct)
  {
    for(auto &component : to_struct_type(src).components())
      component.type() = make_two_valued(component.type());
    return src;
  }
  else
    return src;
}
