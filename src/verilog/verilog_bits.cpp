/*******************************************************************\

Module: Verilog Type Width

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_bits.h"

#include <util/arith_tools.h>

#include <ebmc/ebmc_error.h>

#include "verilog_types.h"

std::optional<mp_integer> verilog_bits_opt(const typet &type)
{
  if(type.id() == ID_bool)
    return 1;

  if(
    type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
    type.id() == ID_verilog_signedbv || type.id() == ID_verilog_unsignedbv)
    return type.get_int(ID_width);

  if(type.id() == ID_array)
  {
    auto &array_type = to_array_type(type);
    auto element_width_opt = verilog_bits_opt(array_type.element_type());
    auto size_opt = numeric_cast<mp_integer>(array_type.size());

    if(element_width_opt.has_value() && size_opt.has_value())
    {
      return element_width_opt.value() * size_opt.value();
    }
    else
      return {};
  }

  if(type.id() == ID_struct)
  {
    // add them up
    mp_integer sum = 0;
    for(auto &component : to_struct_type(type).components())
    {
      auto component_width = verilog_bits_opt(component.type());
      if(!component_width.has_value())
        return {};
      sum += *component_width;
    }
    return sum;
  }

  if(type.id() == ID_union)
  {
    // find the biggest
    mp_integer max = 0;
    for(auto &component : to_verilog_union_type(type).components())
      max = std::max(max, verilog_bits(component.type()));
    return max;
  }

  if(type.id() == ID_verilog_shortint)
    return 16;
  else if(type.id() == ID_verilog_int)
    return 32;
  else if(type.id() == ID_verilog_longint)
    return 64;
  else if(type.id() == ID_verilog_integer)
    return 32;
  else if(type.id() == ID_verilog_time)
    return 64;

  return {};
}

mp_integer verilog_bits(const typet &type)
{
  auto bits_opt = verilog_bits_opt(type);

  if(bits_opt.has_value())
    return std::move(bits_opt.value());
  else
  {
    throw ebmc_errort() << "type `" << type.id()
                        << "' has unknown number of bits";
  }
}
