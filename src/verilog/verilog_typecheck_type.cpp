/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/ebmc_util.h>

#include "verilog_typecheck_expr.h"

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet verilog_typecheck_exprt::convert_type(const irept &src)
{
  if(src.is_nil() || src.id()==ID_reg)
  {
    // it's just a bit
    return bool_typet();
  }
  
  if(src.id()==ID_array)
  {
    const exprt &range=static_cast<const exprt &>(src.find(ID_range));

    mp_integer msb, lsb;
    convert_range(range, msb, lsb);

    bool little_endian=(lsb<=msb);

    mp_integer width=(little_endian?msb-lsb:lsb-msb)+1;
    mp_integer offset=little_endian?lsb:msb;
    
    // let's look at the subtype
    const irept &subtype=
      static_cast<const typet &>(src).subtype();
    
    if(subtype.is_nil() ||
       subtype.id()==ID_signed ||
       subtype.id()==ID_unsigned)
    {
      // we have a bit-vector type, not an array

      bitvector_typet dest(subtype.id()==ID_signed?ID_signedbv:ID_unsignedbv);

      dest.add_source_location()=
        static_cast<const source_locationt &>(src.find(ID_C_source_location));
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
      result.add_source_location()=
        static_cast<const source_locationt &>(src.find(ID_C_source_location));
      result.set(ID_offset, from_integer(offset, integer_typet()));

      return std::move(result);
    }
  }
  else
  {
    error().source_location=static_cast<const typet &>(src).source_location();
    error() << "unexpected type: `" << src.id() << "'" << eom;
    throw 0;
  }
}
