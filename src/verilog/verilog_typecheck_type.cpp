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
  const auto &source_location = src.source_location();

  if(src.is_nil() || src.id()==ID_reg)
  {
    // it's just a bit
    return bool_typet().with_source_location(source_location);
  }
  else if(src.id() == ID_integer)
  {
    return integer_typet().with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_byte)
  {
    return signedbv_typet{8}.with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_shortint)
  {
    return signedbv_typet{16}.with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_int)
  {
    return signedbv_typet{32}.with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_longint)
  {
    return signedbv_typet{64}.with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_integer)
  {
    return signedbv_typet{32}.with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_time)
  {
    return unsignedbv_typet{64}.with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_bit)
  {
    return unsignedbv_typet{1}.with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_logic)
  {
    return unsignedbv_typet{1}.with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_reg)
  {
    return unsignedbv_typet{1}.with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_shortreal)
  {
    return verilog_shortreal_typet().with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_real)
  {
    return verilog_real_typet().with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_realtime)
  {
    return verilog_realtime_typet().with_source_location(source_location);
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

    auto result = symbol_ptr->type; // copy
    return result.with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_enum)
  {
    // Replace by base type, but annotate the original type.
    // The default base type is 'int'.
    auto &enum_type = to_verilog_enum_type(src);
    auto result = enum_type.has_base_type()
                    ? convert_type(enum_type.base_type())
                    : signedbv_typet(32);
    result.set(ID_C_verilog_type, ID_verilog_enum);
    result.set(ID_C_identifier, enum_type.identifier());
    return result.with_source_location(source_location);
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

    if(
      subtype.is_nil() || subtype.id() == ID_signed ||
      subtype.id() == ID_unsigned || subtype.id() == ID_verilog_bit ||
      subtype.id() == ID_verilog_logic)
    {
      // we have a bit-vector type, not an array

      bitvector_typet dest(subtype.id()==ID_signed?ID_signedbv:ID_unsignedbv);

      dest.add_source_location() = source_location;
      dest.set_width(width.to_ulong());
      dest.set(ID_C_little_endian, little_endian);
      dest.set(ID_C_offset, integer2string(offset));

      return std::move(dest).with_source_location(source_location);
    }
    else
    {
      // we have a genuine array, and do a recursive call
      const exprt size=from_integer(width, integer_typet());
      typet s=convert_type(subtype);

      array_typet result(s, size);
      result.add_source_location() = source_location;
      result.set(ID_offset, from_integer(offset, integer_typet()));

      return std::move(result).with_source_location(source_location);
    }
  }
  else if(src.id() == ID_verilog_type_reference)
  {
    auto &type_reference = to_verilog_type_reference(src);
    if(type_reference.expression_op().is_not_nil())
    {
      // the expression is not evaluated
      auto expr = type_reference.expression_op();
      convert_expr(expr);
      return expr.type().with_source_location(source_location);
    }
    else
      return convert_type(type_reference.type_op());
  }
  else
  {
    error().source_location = source_location;
    error() << "unexpected type: `" << src.id() << "'" << eom;
    throw 0;
  }
}
