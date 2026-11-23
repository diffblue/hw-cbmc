/*******************************************************************\

Module: Verilog Bit-Level Layout

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_layout.h"

#include <util/arith_tools.h>
#include <util/invariant.h>

#include "verilog_bits.h"
#include "verilog_types.h"

verilog_bit_ranget verilog_vector_bit_range(
  const mp_integer &width,
  const mp_integer &offset,
  bool increasing,
  const mp_integer &lo,
  const mp_integer &hi)
{
  PRECONDITION(lo <= hi);

  if(increasing)
    return {(width - 1) - (hi - offset), (width - 1) - (lo - offset)};
  else
    return {lo - offset, hi - offset};
}

bool verilog_array_element_zero_is_msb(const array_typet &array_type)
{
  return array_type.get(ID_C_verilog_type) == ID_verilog_packed_array &&
         array_type.get_bool(ID_C_increasing);
}

mp_integer verilog_array_element_lower_bit(
  const array_typet &array_type,
  const mp_integer &array_index)
{
  auto size = numeric_cast_v<mp_integer>(to_constant_expr(array_type.size()));
  auto element_width = verilog_bits(array_type.element_type());

  if(verilog_array_element_zero_is_msb(array_type))
    return (size - 1 - array_index) * element_width;
  else
    return array_index * element_width;
}

mp_integer verilog_unpacked_array_element_index(
  const verilog_array_typet &array_type,
  const mp_integer &declared_index)
{
  PRECONDITION(array_type.is_unpacked());

  auto offset = array_type.offset();

  if(array_type.increasing())
    return declared_index - offset;
  else
    return (offset + array_type.size_int() - 1) - declared_index;
}

mp_integer verilog_packed_array_lower_bit(
  const verilog_array_typet &array_type,
  const mp_integer &lo,
  const mp_integer &hi)
{
  PRECONDITION(array_type.is_packed());
  PRECONDITION(lo <= hi);

  auto element_width = verilog_bits(array_type.element_type());
  auto offset = array_type.offset();

  if(array_type.increasing())
    return (array_type.size_int() - 1 - (hi - offset)) * element_width;
  else
    return (lo - offset) * element_width;
}

std::vector<mp_integer> verilog_struct_component_lower_bits(const typet &type)
{
  PRECONDITION(type.id() == ID_struct);

  auto &components = to_struct_union_type(type).components();

  // the first component is the most significant
  mp_integer position = verilog_bits(type);

  std::vector<mp_integer> result;
  result.reserve(components.size());

  for(auto &component : components)
  {
    position -= verilog_bits(component.type());
    result.push_back(position);
  }

  return result;
}

std::optional<verilog_bit_ranget>
verilog_member_bit_range(const typet &compound, const irep_idt &member_name)
{
  if(compound.id() == ID_struct)
  {
    auto &components = to_struct_union_type(compound).components();
    auto lower_bits = verilog_struct_component_lower_bits(compound);

    for(std::size_t i = 0; i < components.size(); i++)
    {
      if(components[i].get_name() == member_name)
      {
        auto lower = lower_bits[i];
        return verilog_bit_ranget{
          lower, lower + verilog_bits(components[i].type()) - 1};
      }
    }
  }
  else if(compound.id() == ID_union)
  {
    // all members of a packed union start at bit 0
    for(auto &component : to_struct_union_type(compound).components())
    {
      if(component.get_name() == member_name)
        return verilog_bit_ranget{0, verilog_bits(component.type()) - 1};
    }
  }

  return {};
}
