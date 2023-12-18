/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/ebmc_util.h>
#include <util/ieee_float.h>
#include <util/mathematical_types.h>

#include "verilog_typecheck_expr.h"

#include "verilog_types.h"

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet verilog_typecheck_exprt::convert_type(const typet &src)
{
  auto source_location = src.source_location();

  if(src.is_nil() || src.id()==ID_reg)
  {
    // it's just a bit
    return bool_typet();
  }
  else if(src.id() == ID_integer)
  {
    typet result = integer_typet();
    result.add_source_location() = std::move(source_location);
    return result;
  }
  else if(src.id() == ID_verilog_shortreal)
  {
    typet result = verilog_shortreal_typet();
    result.add_source_location() = std::move(source_location);
    return result;
  }
  else if(src.id() == ID_verilog_real)
  {
    typet result = verilog_real_typet();
    result.add_source_location() = std::move(source_location);
    return result;
  }
  else if(src.id() == ID_verilog_realtime)
  {
    typet result = verilog_realtime_typet();
    result.add_source_location() = std::move(source_location);
    return result;
  }
  else if(src.id() == ID_typedef_type)
  {
    // Look it up!
    const symbolt *symbol_ptr;

    auto identifier = src.get(ID_identifier);

    if(ns.lookup(identifier, symbol_ptr))
      throw errort().with_location(source_location)
        << "type symbol " << identifier << " not found";

    DATA_INVARIANT(symbol_ptr->is_type, "typedef symbols must be types");

    return symbol_ptr->type;
  }
  else if(src.id() == ID_verilog_enum)
  {
    // Replace by base type.
    // The default base type is 'int'.
    auto &enum_type = to_verilog_enum_type(src);
    return enum_type.has_base_type() ? enum_type.base_type()
                                     : signedbv_typet(32);
  }
  else if(src.id() == ID_array)
  {
    const exprt &range=static_cast<const exprt &>(src.find(ID_range));

    mp_integer msb, lsb;
    convert_range(range, msb, lsb);

    bool little_endian=(lsb<=msb);

    mp_integer width=(little_endian?msb-lsb:lsb-msb)+1;
    mp_integer offset=little_endian?lsb:msb;
    
    // let's look at the subtype
    const auto subtype =
      static_cast<const typet &>(src).has_subtype()
        ? static_cast<const type_with_subtypet &>(src).subtype()
        : typet(ID_nil);

    if(subtype.is_nil() ||
       subtype.id()==ID_signed ||
       subtype.id()==ID_unsigned)
    {
      // we have a bit-vector type, not an array

      bitvector_typet dest(subtype.id()==ID_signed?ID_signedbv:ID_unsignedbv);

      dest.add_source_location() = source_location;
      dest.set_width(width.to_ulong());
      dest.set(ID_C_little_endian, little_endian);
      dest.set(ID_C_offset, integer2string(offset));

      return std::move(dest);
    }
    else
    {
      // we have a genuine array, and do a recursive call
      const exprt size=from_integer(width, integer_typet());
      typet s=convert_type(subtype);

      array_typet result(s, size);
      result.add_source_location() = source_location;
      result.set(ID_offset, from_integer(offset, integer_typet()));

      return std::move(result);
    }
  }
  else
  {
    error().source_location = source_location;
    error() << "unexpected type: `" << src.id() << "'" << eom;
    throw 0;
  }
}
