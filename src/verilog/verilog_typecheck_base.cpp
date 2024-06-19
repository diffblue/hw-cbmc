/*******************************************************************\

Module: Verilog Type Checker Base

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/ebmc_util.h>
#include <util/expr_util.h>
#include <util/prefix.h>
#include <util/std_types.h>

#include "expr2verilog.h"
#include "verilog_typecheck_base.h"

/*******************************************************************\

Function: verilog_module_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt verilog_module_symbol(const irep_idt &base_name)
{
  return "Verilog::"+id2string(base_name);
}

/*******************************************************************\

Function: strip_verilog_prefix

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt strip_verilog_prefix(const irep_idt &identifier)
{
  std::string prefix="Verilog::";
  assert(has_prefix(id2string(identifier), prefix));
  assert(identifier.size()>=prefix.size());
  return identifier.c_str()+prefix.size();
}

/*******************************************************************\

Function: verilog_module_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt verilog_module_name(const irep_idt &identifier)
{
  return strip_verilog_prefix(identifier);
}

/*******************************************************************\

Function: verilog_typecheck_baset::to_string

  Inputs: Type

 Outputs:

 Purpose:

\*******************************************************************/

std::string verilog_typecheck_baset::to_string(const typet &type)
{
  return type2verilog(type, ns);
}

/*******************************************************************\

Function: verilog_typecheck_baset::to_string

  Inputs: Expression

 Outputs: String representing the expression

 Purpose:

\*******************************************************************/

std::string verilog_typecheck_baset::to_string(const exprt &expr)
{
  return expr2verilog(expr, ns);
}

/*******************************************************************\

Function: verilog_typecheck_baset::array_size

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer verilog_typecheck_baset::array_size(const array_typet &type)
{
  auto size_opt = numeric_cast<mp_integer>(type.size());

  if(!size_opt.has_value())
  {
    throw errort().with_location(type.source_location())
      << "failed to get array size of array type";
  }

  return size_opt.value();
}

/*******************************************************************\

Function: verilog_typecheck_baset::array_offset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer verilog_typecheck_baset::array_offset(const array_typet &type)
{
  mp_integer offset;

  if(to_integer_non_constant(
       static_cast<const exprt &>(type.find(ID_offset)), offset))
  {
    throw errort().with_location(type.source_location())
      << "failed to get array offset of type `" << type.id() << '\'';
  }

  return offset;
}

/*******************************************************************\

Function: verilog_typecheck_baset::get_width_opt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::optional<mp_integer>
verilog_typecheck_baset::get_width_opt(const typet &type)
{
  if(type.id()==ID_bool)
    return 1;

  if(type.id()==ID_unsignedbv || type.id()==ID_signedbv ||
     type.id()==ID_verilog_signedbv || type.id()==ID_verilog_unsignedbv)
    return type.get_int(ID_width);

  if(type.id()==ID_array)
  {
    auto element_width = get_width_opt(to_array_type(type).element_type());
    if(element_width.has_value())
      return array_size(to_array_type(type)) * element_width.value();
    else
      return {};
  }

  if(type.id() == ID_struct)
  {
    // add them up
    mp_integer sum = 0;
    for(auto &component : to_struct_type(type).components())
    {
      auto component_width = get_width_opt(component.type());
      if(!component_width.has_value())
        return {};
      sum += *component_width;
    }
    return sum;
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

/*******************************************************************\

Function: verilog_typecheck_baset::get_width

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer verilog_typecheck_baset::get_width(const typet &type)
{
  auto width_opt = get_width_opt(type);

  if(width_opt.has_value())
    return std::move(width_opt.value());
  else
    throw errort().with_location(type.source_location())
      << "type `" << type.id() << "' has unknown width";
}

/*******************************************************************\

Function: verilog_typecheck_baset::index_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet verilog_typecheck_baset::index_type(const array_typet &array_type)
{
  return unsignedbv_typet(address_bits(
      (array_size(array_type) + array_offset(array_type)).to_ulong()));
}
