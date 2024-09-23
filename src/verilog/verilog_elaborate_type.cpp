/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/ebmc_util.h>
#include <util/ieee_float.h>
#include <util/mathematical_types.h>

#include "verilog_expr.h"
#include "verilog_typecheck_expr.h"
#include "verilog_types.h"

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_unpacked_array_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

array_typet verilog_typecheck_exprt::convert_unpacked_array_type(
  const type_with_subtypet &src)
{
  // int whatnot[x:y];
  // 'src' is yet to be converted, but 'element_type' is already converted.
  PRECONDITION(src.id() == ID_verilog_unpacked_array);

  // Unpacked arrays may have a range [x:y],
  // or a size [s], equivalent to [0:s-1]
  const exprt &range_expr = static_cast<const exprt &>(src.find(ID_range));
  const exprt &size_expr = static_cast<const exprt &>(src.find(ID_size));

  mp_integer size, offset;
  bool big_endian;

  if(range_expr.is_not_nil())
  {
    // these may be negative
    mp_integer msb, lsb;
    convert_range(range_expr, msb, lsb);
    big_endian = (lsb > msb);
    size = (big_endian ? lsb - msb : msb - lsb) + 1;
    DATA_INVARIANT(size >= 0, "array size must not be negative");
    offset = big_endian ? msb : lsb;
  }
  else if(size_expr.is_not_nil())
  {
    big_endian = false;
    size = convert_integer_constant_expression(size_expr);
    offset = 0;
    if(size < 0)
    {
      // The size must be positive. 1800-2017 7.4.2
      throw errort().with_location(size_expr.find_source_location())
        << "array size must be nonnegative";
    }
  }
  else
  {
    throw errort() << "unpacked array must have range or size";
  }

  // recursively convert element_type
  typet element_type = elaborate_type(src.subtype());

  const exprt final_size_expr = from_integer(size, integer_typet());
  auto result = array_typet{element_type, final_size_expr};
  result.set(ID_offset, from_integer(offset, integer_typet()));
  result.set(ID_C_big_endian, big_endian);

  return result;
}

/*******************************************************************\

Function: verilog_typecheck_exprt::convert_packed_array_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet verilog_typecheck_exprt::convert_packed_array_type(
  const type_with_subtypet &src)
{
  PRECONDITION(src.id() == ID_verilog_packed_array);

  const exprt &range = static_cast<const exprt &>(src.find(ID_range));
  const auto &source_location = src.source_location();

  mp_integer msb, lsb;
  convert_range(range, msb, lsb);

  bool big_endian = (lsb > msb);

  mp_integer width = (big_endian ? lsb - msb : msb - lsb) + 1;
  mp_integer offset = big_endian ? msb : lsb;

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

    bitvector_typet dest(
      subtype.id() == ID_signed ? ID_signedbv : ID_unsignedbv);

    dest.add_source_location() = source_location;
    dest.set_width(width.to_ulong());
    dest.set(ID_C_big_endian, big_endian);
    dest.set(ID_C_offset, integer2string(offset));

    return std::move(dest).with_source_location(source_location);
  }
  else
  {
    // We have a multi-dimensional packed array,
    // and do a recursive call.
    const exprt size = from_integer(width, integer_typet());
    typet s = elaborate_type(subtype);

    array_typet result(s, size);
    result.add_source_location() = source_location;
    result.set(ID_offset, from_integer(offset, integer_typet()));

    return std::move(result).with_source_location(source_location);
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::elaborate_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet verilog_typecheck_exprt::elaborate_type(const typet &src)
{
  const auto &source_location = src.source_location();

  if(src.is_nil() || src.id() == ID_reg)
  {
    // it's just a bit
    return bool_typet().with_source_location(source_location);
  }
  else if(src.id() == ID_signed)
  {
    // one bit, signed
    return signedbv_typet{1}.with_source_location(source_location);
  }
  else if(src.id() == ID_unsigned)
  {
    // one bit, unsigned
    return unsignedbv_typet{1}.with_source_location(source_location);
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
                    ? elaborate_type(enum_type.base_type())
                    : signedbv_typet(32);
    result.set(ID_C_verilog_type, ID_verilog_enum);
    result.set(ID_C_identifier, enum_type.identifier());
    return result.with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_packed_array)
  {
    return convert_packed_array_type(to_type_with_subtype(src));
  }
  else if(src.id() == ID_verilog_unpacked_array)
  {
    return convert_unpacked_array_type(to_type_with_subtype(src));
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
      return elaborate_type(type_reference.type_op());
  }
  else if(src.id() == ID_to_be_elaborated)
  {
    // recursive call
    return elaborate_type(to_to_be_elaborated_type(src).subtype());
  }
  else if(src.id() == ID_struct || src.id() == ID_union)
  {
    // the declarations of the components
    auto &declaration_list = src.find(ID_declaration_list).get_sub();
    struct_union_typet::componentst components;

    for(auto &declaration : declaration_list)
    {
      auto &declaration_expr = static_cast<const exprt &>(declaration);
      DATA_INVARIANT(
        declaration.id() == ID_decl, "struct type must have declarations");

      // Convert the type
      auto type = elaborate_type(declaration_expr.type());

      // Convert the declarators
      for(auto &declarator_expr : declaration_expr.operands())
      {
        auto &declarator =
          static_cast<const verilog_declaratort &>(declarator_expr);

        struct_union_typet::componentt component;

        // compose the type
        if(declarator.type().is_nil())
          component.type() = type;
        else if(declarator.type().id() == ID_array)
        {
          throw errort().with_location(declarator.source_location())
            << "array in struct";
        }
        else
        {
          throw errort().with_location(declarator.source_location())
            << "unexpected type on declarator";
        }

        component.add_source_location() = declarator.source_location();
        component.set_base_name(declarator.base_name());
        component.set_name(declarator.base_name());
        components.push_back(std::move(component));
      }
    }

    return struct_union_typet{src.id(), std::move(components)}
      .with_source_location(src.source_location());
  }
  else if(src.id() == ID_type)
  {
    return src;
  }
  else
  {
    throw errort().with_location(source_location)
      << "unexpected type: `" << src.id() << "'";
  }
}
