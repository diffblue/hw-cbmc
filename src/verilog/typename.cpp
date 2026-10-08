/*******************************************************************\

Module: $typename

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "typename.h"

#include <util/arith_tools.h>
#include <util/namespace.h>
#include <util/symbol.h>

#include "verilog_bits.h"
#include "verilog_types.h"

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
    auto &array_type = to_verilog_array_type(type);
    auto offset = array_type.offset();
    if(array_type.increasing())
      return offset;
    else
      return offset + array_type.size_int() - 1;
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
    auto &array_type = to_verilog_array_type(type);
    auto offset = array_type.offset();
    if(array_type.increasing())
      return offset + array_type.size_int() - 1;
    else
      return offset;
  }
  else
    return 0;
}

// The keyword used for a four-valued single-bit element type, i.e.,
// "reg", "wire" or "logic".  This is used both for scalars and as the
// prefix of a vector.  See IEEE 1800-2017 20.6.1.
static std::string verilog_bitvector_keyword(const typet &type)
{
  const auto vector_type = type.get(ID_C_verilog_vector_type);
  if(vector_type == ID_reg)
    return "reg";
  else if(vector_type == ID_wire)
    return "wire";
  else if(vector_type == ID_verilog_logic)
    return "logic";
  else
    return "bit";
}

std::string verilog_typename(const typet &type, const namespacet &ns)
{
  const auto verilog_type = type.get(ID_C_verilog_type);
  const auto vector_type = type.get(ID_C_verilog_vector_type);

  auto left = [](const typet &type)
  { return integer2string(verilog_left(type)); };
  auto right = [](const typet &type)
  { return integer2string(verilog_right(type)); };

  if(type.get(ID_C_verilog_type) == ID_verilog_enum)
  {
    // not well standardised; tool-specific
    auto identifier = type.get(ID_C_identifier);
    auto &enum_symbol = ns.lookup(identifier);
    auto &enum_type = to_verilog_enum_type(enum_symbol.type);
    std::string result = "enum{";
    bool first = true;
    for(auto &name : enum_type.enum_names())
    {
      if(first)
        first = false;
      else
        result += ',';
      result += id2string(name.base_name());
    }
    result += '}';
    return result;
  }
  else if(type.id() == ID_struct)
  {
    // not well standardised; tool-specific
    auto &struct_type = to_struct_type(type);
    std::string result = "struct{";
    for(auto &component : struct_type.components())
    {
      result += verilog_typename(component.type(), ns);
      result += ' ';
      result += id2string(component.get_name());
      result += ';'; // no newline or the like
    }
    result += '}';
    return result;
  }
  else if(type.id() == ID_unsignedbv)
  {
    if(verilog_type == ID_verilog_byte)
      return "byte unsigned";
    else if(verilog_type == ID_verilog_int)
      return "int unsigned";
    else if(verilog_type == ID_verilog_longint)
      return "longint unsigned";
    else if(verilog_type == ID_verilog_shortint)
      return "shortint unsigned";
    else if(verilog_type == ID_verilog_logic)
    {
      // scalar four-valued type: reg, wire or logic
      if(vector_type == ID_reg)
        return "reg";
      else if(vector_type == ID_wire)
        return "wire";
      else
        return "logic";
    }
    else
    {
      auto suffix = "[" + left(type) + ":" + right(type) + "]";
      return verilog_bitvector_keyword(type) + suffix;
    }
  }
  else if(type.id() == ID_verilog_unsignedbv)
  {
    return "logic[" + left(type) + ":" + right(type) + "]";
  }
  else if(type.id() == ID_bool)
  {
    if(vector_type == ID_reg)
      return "reg";
    else if(vector_type == ID_wire)
      return "wire";
    else if(verilog_type == ID_verilog_logic)
      return "logic";
    else
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
    else if(verilog_type == ID_verilog_logic)
    {
      // scalar four-valued type: reg, wire or logic
      if(vector_type == ID_reg)
        return "reg signed";
      else if(vector_type == ID_wire)
        return "wire signed";
      else
        return "logic signed";
    }
    else
    {
      auto suffix = "[" + left(type) + ":" + right(type) + "]";
      return verilog_bitvector_keyword(type) + " signed" + suffix;
    }
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
  else if(type.id() == ID_array)
  {
    // Collect unpacked dimensions, then packed dimensions.
    // Emit as base_type[packed_dims][base_range]$[unpacked_dims]
    // matching the declaration order.
    std::string unpacked_dimensions;
    auto *current = &type;
    while(current->id() == ID_array &&
          to_verilog_array_type(*current).is_unpacked())
    {
      unpacked_dimensions += '[' + integer2string(verilog_left(*current)) +
                             ':' + integer2string(verilog_right(*current)) +
                             ']';
      current = &to_verilog_array_type(*current).element_type();
    }

    std::string packed_dimensions;
    while(current->id() == ID_array &&
          to_verilog_array_type(*current).is_packed())
    {
      packed_dimensions += '[' + integer2string(verilog_left(*current)) + ':' +
                           integer2string(verilog_right(*current)) + ']';
      current = &to_verilog_array_type(*current).element_type();
    }

    auto base_type = verilog_typename(*current, ns);

    // The base type might already have the innermost packed array.
    // The packed_dimensions must be inserted before the '[', if any.
    auto bracket_pos = base_type.find('[');
    if(bracket_pos == std::string::npos)
    {
      // no bracket
      base_type += packed_dimensions;
    }
    else
    {
      base_type = base_type.substr(0, bracket_pos) + packed_dimensions +
                  base_type.substr(bracket_pos, std::string::npos);
    }

    if(unpacked_dimensions.empty())
      return base_type;
    else
      return base_type + '$' + unpacked_dimensions;
  }
  else
    return "?";
}
