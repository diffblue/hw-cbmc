/*******************************************************************\

Module: VHDL Types

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// VHDL Types

#include "vhdl_types.h"

#include <util/arith_tools.h>
#include <util/invariant.h>

irep_idt to_irep_id(vhdl_directiont direction)
{
  return direction == vhdl_directiont::TO ? ID_to : ID_vhdl_downto;
}

vhdl_directiont to_vhdl_direction(irep_idt id)
{
  PRECONDITION(id == ID_to || id == ID_vhdl_downto);
  return id == ID_to ? vhdl_directiont::TO : vhdl_directiont::DOWNTO;
}

std::string vhdl_ranget::to_string() const
{
  return integer2string(left) +
         (direction == vhdl_directiont::TO ? " to " : " downto ") +
         integer2string(right);
}

static void set_range(typet &type, const vhdl_ranget &range)
{
  type.set(ID_vhdl_left, integer2string(range.left));
  type.set(ID_vhdl_right, integer2string(range.right));
  type.set(ID_vhdl_direction, to_irep_id(range.direction));
}

static vhdl_ranget get_range(const typet &type)
{
  PRECONDITION(!type.get(ID_vhdl_direction).empty());
  vhdl_ranget result;
  result.left = string2integer(type.get_string(ID_vhdl_left));
  result.right = string2integer(type.get_string(ID_vhdl_right));
  result.direction = to_vhdl_direction(type.get(ID_vhdl_direction));
  return result;
}

std::optional<std::size_t>
vhdl_enumeration_typet::position(irep_idt literal) const
{
  auto &e = elements();
  for(std::size_t i = 0; i < e.size(); i++)
    if(e[i].id() == literal)
      return i;
  return {};
}

vhdl_integer_typet::vhdl_integer_typet(irep_idt _name, const vhdl_ranget &range)
  : vhdl_typet(ID_vhdl_integer, _name)
{
  set_range(range);
}

vhdl_ranget vhdl_integer_typet::range() const
{
  return get_range(*this);
}

void vhdl_integer_typet::set_range(const vhdl_ranget &range)
{
  ::set_range(*this, range);
}

vhdl_array_typet::vhdl_array_typet(
  irep_idt _name,
  typet _element_type,
  const vhdl_ranget &range)
  : vhdl_typet(ID_vhdl_array, _name)
{
  add(ID_element_type) = std::move(_element_type);
  add(ID_vhdl_index_type) = vhdl_integer_type(range);
  set_range(range);
}

vhdl_ranget vhdl_array_typet::range_for_length(const mp_integer &length) const
{
  auto index_range = index_type().range();
  vhdl_ranget result;
  result.left = index_range.left;
  result.direction = index_range.direction;
  if(result.direction == vhdl_directiont::TO)
    result.right = result.left + length - 1;
  else
    result.right = result.left - length + 1;
  return result;
}

vhdl_ranget vhdl_array_typet::range() const
{
  PRECONDITION(is_constrained());
  return get_range(*this);
}

void vhdl_array_typet::set_range(const vhdl_ranget &range)
{
  ::set_range(*this, range);
}

vhdl_array_typet vhdl_array_typet::unconstrained() const
{
  auto result = *this;
  result.remove(ID_vhdl_left);
  result.remove(ID_vhdl_right);
  result.remove(ID_vhdl_direction);
  return result;
}

bool vhdl_record_typet::has_component(irep_idt name) const
{
  for(auto &c : components())
    if(c.get_name() == name)
      return true;
  return false;
}

const vhdl_record_typet::componentt &
vhdl_record_typet::get_component(irep_idt name) const
{
  for(auto &c : components())
    if(c.get_name() == name)
      return c;
  UNREACHABLE;
}

static irept::subt literals(const std::vector<const char *> &list)
{
  irept::subt result;
  for(auto l : list)
    result.push_back(irept{l});
  return result;
}

vhdl_enumeration_typet vhdl_boolean_type()
{
  return vhdl_enumeration_typet{"boolean", literals({"false", "true"})};
}

vhdl_enumeration_typet vhdl_bit_type()
{
  return vhdl_enumeration_typet{"bit", literals({"'0'", "'1'"})};
}

vhdl_enumeration_typet vhdl_std_ulogic_type()
{
  return vhdl_enumeration_typet{
    "std_ulogic",
    literals({"'U'", "'X'", "'0'", "'1'", "'Z'", "'W'", "'L'", "'H'", "'-'"})};
}

vhdl_enumeration_typet vhdl_std_logic_type()
{
  // IEEE 1076-2008 std_logic_1164: a subtype of std_ulogic
  auto result = vhdl_std_ulogic_type();
  result.set_name("std_logic");
  return result;
}

vhdl_integer_typet vhdl_integer_type()
{
  return vhdl_integer_typet{
    "integer", {-power(2, 31), power(2, 31) - 1, vhdl_directiont::TO}};
}

vhdl_integer_typet vhdl_integer_type(const vhdl_ranget &range)
{
  auto result = vhdl_integer_type();
  result.set_range(range);
  return result;
}

vhdl_integer_typet vhdl_natural_type()
{
  auto result = vhdl_integer_type({0, power(2, 31) - 1, vhdl_directiont::TO});
  result.set_name("natural");
  return result;
}

vhdl_integer_typet vhdl_positive_type()
{
  auto result = vhdl_integer_type({1, power(2, 31) - 1, vhdl_directiont::TO});
  result.set_name("positive");
  return result;
}

vhdl_enumeration_typet vhdl_character_type()
{
  // the printable ASCII characters, as character literals
  irept::subt elements;
  for(char ch = ' '; ch <= '~'; ch++)
    elements.push_back(irept{vhdl_enumeration_typet::character_literal(ch)});
  return vhdl_enumeration_typet{"character", std::move(elements)};
}

vhdl_array_typet vhdl_string_type()
{
  // IEEE 1076-2008 16.3: array (positive range <>) of character
  return vhdl_array_typet{
    "string", vhdl_character_type(), vhdl_positive_type()};
}

vhdl_physical_typet vhdl_time_type()
{
  return vhdl_physical_typet{"time"};
}

vhdl_file_typet vhdl_text_type()
{
  return vhdl_file_typet{"text", vhdl_string_type()};
}

bool is_vhdl_simulation_type(const typet &type)
{
  return type.id() == ID_vhdl_physical_type || type.id() == ID_vhdl_access ||
         type.id() == ID_vhdl_file;
}

vhdl_array_typet vhdl_unconstrained_array_type(irep_idt name)
{
  // the index subtype of all of these is natural
  auto natural = vhdl_natural_type();

  if(name == "bit_vector")
    return vhdl_array_typet{name, vhdl_bit_type(), natural};
  else if(name == "std_ulogic_vector")
    return vhdl_array_typet{name, vhdl_std_ulogic_type(), natural};
  else if(name == "std_logic_vector")
  {
    // IEEE 1076-2008 std_logic_1164: a subtype of std_ulogic_vector
    vhdl_array_typet result{
      "std_ulogic_vector", vhdl_std_logic_type(), natural};
    result.set_name(name);
    return result;
  }
  else if(name == "unsigned" || name == "signed")
    return vhdl_array_typet{name, vhdl_std_logic_type(), natural};
  else
    UNREACHABLE;
}

vhdl_array_typet vhdl_vector_type(irep_idt name, const vhdl_ranget &range)
{
  return vhdl_constrained_array_type(
    vhdl_unconstrained_array_type(name), range);
}

vhdl_array_typet vhdl_constrained_array_type(
  const vhdl_array_typet &type,
  const vhdl_ranget &range)
{
  auto result = type;
  result.set_range(range);
  return result;
}

bool is_vhdl_scalar_bit_type(const typet &type)
{
  if(type.id() != ID_vhdl_enumeration)
    return false;
  auto base = to_vhdl_enumeration_type(type).base_name();
  return base == "bit" || base == "std_ulogic";
}

bool is_unconstrained_array(const typet &type)
{
  return type.id() == ID_vhdl_array &&
         !to_vhdl_array_type(type).is_constrained();
}

bool is_vhdl_vector_type(const typet &type)
{
  if(type.id() != ID_vhdl_array)
    return false;
  auto &array_type = to_vhdl_array_type(type);
  return array_type.is_constrained() &&
         is_vhdl_scalar_bit_type(array_type.element_type());
}

bool is_vhdl_numeric_vector_type(const typet &type)
{
  if(type.id() != ID_vhdl_array)
    return false;
  auto base = to_vhdl_array_type(type).base_name();
  return base == "unsigned" || base == "signed";
}

bool is_vhdl_integer_type(const typet &type)
{
  return type.id() == ID_vhdl_integer;
}

bool is_vhdl_universal_type(const typet &type)
{
  return type.id() == ID_natural || type.id() == ID_char ||
         type.id() == ID_string || type.id() == ID_vhdl_bit_string ||
         type.id() == ID_vhdl_aggregate || type.id() == ID_real ||
         type.id() == ID_vhdl_overloaded_literal || type.id() == ID_nullptr;
}

bool vhdl_types_compatible(const typet &a, const typet &b)
{
  if(a.id() != b.id())
    return false;

  if(a.id() == ID_vhdl_access)
  {
    // an anonymous access type, from an allocator or null, matches
    // any access type with a compatible designated type
    auto &a_access = to_vhdl_access_type(a);
    auto &b_access = to_vhdl_access_type(b);
    if(a_access.base_name().empty() || b_access.base_name().empty())
      return vhdl_types_compatible(
        a_access.designated_type(), b_access.designated_type());
    return a_access.base_name() == b_access.base_name();
  }

  if(
    a.id() != ID_vhdl_enumeration && a.id() != ID_vhdl_integer &&
    a.id() != ID_vhdl_array && a.id() != ID_vhdl_record &&
    a.id() != ID_vhdl_physical_type && a.id() != ID_vhdl_file)
    return a == b;

  // the same base type; the subtypes may differ
  return static_cast<const vhdl_typet &>(a).base_name() ==
         static_cast<const vhdl_typet &>(b).base_name();
}

typet vhdl_base_type(const typet &type)
{
  if(type.id() == ID_vhdl_integer)
  {
    auto &integer_type = to_vhdl_integer_type(type);
    return vhdl_integer_typet{
      integer_type.base_name(),
      {-power(2, 31), power(2, 31) - 1, vhdl_directiont::TO}};
  }
  else if(type.id() == ID_vhdl_enumeration)
  {
    auto result = to_vhdl_enumeration_type(type);
    result.set_name(result.base_name());
    return std::move(result);
  }
  else
    return type;
}

constant_exprt vhdl_integer_constant(const mp_integer &value, const typet &type)
{
  PRECONDITION(type.id() == ID_vhdl_integer);
  return constant_exprt{integer2string(value), type};
}

mp_integer vhdl_integer_value(const constant_exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_vhdl_integer);
  return string2integer(id2string(expr.get_value()));
}

std::string vhdl_type_to_string(const typet &type)
{
  if(type.id() == ID_vhdl_array)
  {
    auto &array_type = to_vhdl_array_type(type);
    if(array_type.is_constrained())
      return id2string(array_type.name()) + "(" +
             array_type.range().to_string() + ")";
    else
      return id2string(array_type.name());
  }
  else if(type.id() == ID_vhdl_integer)
  {
    auto &integer_type = to_vhdl_integer_type(type);
    auto name = integer_type.name();
    auto range = integer_type.range();

    // the ranges of the predefined subtypes are implied
    bool predefined = (name == "integer" && range.low() == -power(2, 31)) ||
                      (name == "natural" && range.low() == 0) ||
                      (name == "positive" && range.low() == 1);
    if(predefined && range.high() == power(2, 31) - 1)
      return id2string(name);
    else
      return id2string(name) + " range " + range.to_string();
  }
  else if(type.id() == ID_vhdl_access)
  {
    auto &access_type = to_vhdl_access_type(type);
    if(access_type.name().empty())
      return "access " + vhdl_type_to_string(access_type.designated_type());
    else
      return id2string(access_type.name());
  }
  else if(
    type.id() == ID_vhdl_enumeration || type.id() == ID_vhdl_record ||
    type.id() == ID_vhdl_physical_type || type.id() == ID_vhdl_file)
    return id2string(static_cast<const vhdl_typet &>(type).name());
  else
    return id2string(type.id());
}
