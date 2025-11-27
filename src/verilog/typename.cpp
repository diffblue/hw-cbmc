/*******************************************************************\

Module: $typename

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "typename.h"

#include <util/arith_tools.h>

#include "verilog_bits.h"

// unpacked array: left bound
// packed array: index of most significant element
// 0 otherwise
mp_integer verilog_left(const typet &type)
{
  if(
    type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
    type.id() == ID_verilog_unsignedbv || type.id() == ID_verilog_signedbv ||
    type.id() == ID_bool)
  {
    auto offset = type.get_int(ID_C_offset);
    if(type.get_bool(ID_C_increasing))
      return offset;
    else
      return offset + verilog_bits(type) - 1;
  }
  else if(type.id() == ID_array)
  {
    auto offset = numeric_cast_v<mp_integer>(
      to_constant_expr(static_cast<const exprt &>(type.find(ID_offset))));
    if(type.get_bool(ID_C_increasing))
      return offset;
    else
    {
      return offset +
             numeric_cast_v<mp_integer>(
               to_constant_expr(to_array_type(type).size())) -
             1;
    }
  }
  else
    return 0;
}

// unpacked array: right bound
// packed array: index of least significant element
// 0 otherwise
mp_integer verilog_right(const typet &type)
{
  if(
    type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
    type.id() == ID_verilog_unsignedbv || type.id() == ID_verilog_signedbv ||
    type.id() == ID_bool)
  {
    auto offset = type.get_int(ID_C_offset);
    if(type.get_bool(ID_C_increasing))
      return offset + verilog_bits(type) - 1;
    else
      return offset;
  }
  else if(type.id() == ID_array)
  {
    auto offset = numeric_cast_v<mp_integer>(
      to_constant_expr(static_cast<const exprt &>(type.find(ID_offset))));
    if(type.get_bool(ID_C_increasing))
    {
      return offset +
             numeric_cast_v<mp_integer>(
               to_constant_expr(to_array_type(type).size())) -
             1;
    }
    else
      return offset;
  }
  else
    return 0;
}

std::string verilog_typename(const typet &type)
{
  const auto verilog_type = type.get(ID_C_verilog_type);

  auto left = [](const typet &type)
  { return integer2string(verilog_left(type)); };
  auto right = [](const typet &type)
  { return integer2string(verilog_right(type)); };

  if(type.id() == ID_unsignedbv)
  {
    if(verilog_type == ID_verilog_byte)
      return "byte unsigned";
    else if(verilog_type == ID_verilog_int)
      return "int unsigned";
    else if(verilog_type == ID_verilog_longint)
      return "longint unsigned";
    else if(verilog_type == ID_verilog_shortint)
      return "shortint unsigned";
    else
      return "bit[" + left(type) + ":" + right(type) + "]";
  }
  else if(type.id() == ID_verilog_unsignedbv)
  {
    return "logic[" + left(type) + ":" + right(type) + "]";
  }
  else if(type.id() == ID_bool)
  {
    return "bit";
  }
  else if(type.id() == ID_signedbv)
  {
    if(verilog_type == ID_verilog_byte)
      return "byte";
    else if(verilog_type == ID_verilog_int)
      return "int";
    else if(verilog_type == ID_verilog_longint)
      return "longint";
    else if(verilog_type == ID_verilog_shortint)
      return "shortint";
    else
      return "bit signed[" + left(type) + ":" + right(type) + "]";
  }
  else if(type.id() == ID_verilog_byte)
  {
    return "byte";
  }
  else if(type.id() == ID_verilog_int)
  {
    return "int";
  }
  else if(type.id() == ID_verilog_integer)
  {
    return "integer";
  }
  else if(type.id() == ID_verilog_longint)
  {
    return "longint";
  }
  else if(type.id() == ID_verilog_shortint)
  {
    return "shortint";
  }
  else if(type.id() == ID_verilog_signedbv)
  {
    return "logic signed[" + left(type) + ":" + right(type) + "]";
  }
  else if(type.id() == ID_verilog_realtime)
  {
    return "realtime";
  }
  else if(type.id() == ID_verilog_real)
  {
    return "real";
  }
  else if(type.id() == ID_verilog_shortreal)
  {
    return "shortreal";
  }
  else if(type.id() == ID_verilog_chandle)
  {
    return "chandle";
  }
  else if(type.id() == ID_verilog_event)
  {
    return "event";
  }
  else if(type.id() == ID_verilog_string)
  {
    return "string";
  }
  else
    return "?";
}
