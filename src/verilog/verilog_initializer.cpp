/*******************************************************************\

Module: Verilog Initializer

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_initializer.h"

#include <util/arith_tools.h>
#include <util/std_expr.h>

std::optional<exprt> verilog_default_initializer(const typet &type)
{
  if(type.id() == ID_signedbv || type.id() == ID_unsignedbv)
    return from_integer(0, type);
  else if(type.id() == ID_bool)
    return false_exprt{};
  else if(type.id() == ID_array)
  {
    auto &array_type = to_array_type(type);
    auto default_element_opt =
      verilog_default_initializer(array_type.element_type());
    if(!default_element_opt.has_value())
      return {};
    else
      return array_of_exprt{*default_element_opt, array_type};
  }
  else if(type.id() == ID_struct)
  {
    auto &struct_type = to_struct_type(type);
    exprt::operandst member_values;
    for(auto &component : struct_type.components())
    {
      auto member_value_opt = verilog_default_initializer(component.type());
      if(!member_value_opt.has_value())
        return {};
      member_values.push_back(*member_value_opt);
    }
    return struct_exprt{std::move(member_values), struct_type};
  }
  else if(type.id() == ID_verilog_chandle)
  {
    return constant_exprt{ID_NULL, type};
  }
  else
    return {};
}
