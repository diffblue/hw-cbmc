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
  bool increasing;

  if(range_expr.is_not_nil())
  {
    // these may be negative
    auto range = convert_range(range_expr);
    increasing = range.increasing();
    size = range.length();
    offset = range.smallest_index();
  }
  else if(size_expr.is_not_nil())
  {
    increasing = false;
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
  result.set(ID_C_increasing, increasing);
  result.set(ID_C_verilog_type, ID_verilog_unpacked_array);

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

  const exprt &range_expr = static_cast<const exprt &>(src.find(ID_range));
  const auto &source_location = src.source_location();

  auto range = convert_range(range_expr);

  mp_integer width = range.length();
  mp_integer offset = range.smallest_index();

  // let's look at the subtype
  const auto subtype =
    static_cast<const typet &>(src).has_subtype()
      ? static_cast<const type_with_subtypet &>(src).subtype()
      : typet(ID_nil);

  if(
    subtype.is_nil() || subtype.id() == ID_signed ||
    subtype.id() == ID_unsigned || subtype.id() == ID_verilog_bit ||
    subtype.id() == ID_verilog_logic || subtype.id() == ID_reg ||
    subtype.id() == ID_wire)
  {
    // we have a bit-vector type, not an array

    bitvector_typet dest(
      subtype.id() == ID_signed ? ID_signedbv : ID_unsignedbv);

    dest.add_source_location() = source_location;
    dest.set_width(width.to_ulong());
    dest.set(ID_C_increasing, range.increasing());
    dest.set(ID_C_offset, integer2string(offset));
    dest.set(ID_C_verilog_type, ID_verilog_packed_array);

    return std::move(dest).with_source_location(source_location);
  }
  else
  {
    // We have a multi-dimensional packed array,
    // and do a recursive call.
    const exprt size = from_integer(width, integer_typet());
    typet element_type = elaborate_type(subtype);

    // the element type must be packed; reject otherwise
    if(element_type.id() == ID_verilog_real)
    {
      throw errort().with_location(source_location)
        << "packed array must use packed element type";
    }

    array_typet result{element_type, size};
    result.set(ID_offset, from_integer(offset, integer_typet()));
    result.set(ID_C_verilog_type, ID_verilog_packed_array);

    return std::move(result).with_source_location(source_location);
  }
}

/*******************************************************************\

Function: verilog_typecheck_exprt::elaborate_package_scope_typedef

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet verilog_typecheck_exprt::elaborate_package_scope_typedef(
  const verilog_package_scope_typet &src)
{
  auto location = src.source_location();

  if(src.subtypes()[1].id() != ID_typedef_type)
    throw errort().with_location(location)
      << "verilog_package_scope expects typedef_type on the rhs";

  auto package_base_name = src.subtypes()[0].id();
  auto typedef_base_name = src.subtypes()[1].get(ID_base_name);

  // stitch together
  irep_idt full_identifier =
    id2string(verilog_package_identifier(package_base_name)) + '.' +
    id2string(typedef_base_name);

  // recursive call
  verilog_typedef_typet full_typedef_type(full_identifier);
  full_typedef_type.set(ID_identifier, full_identifier);

  return elaborate_type(full_typedef_type);
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
    // it's just a bit, four-valued
    return bool_typet().with_source_location(source_location);
  }
  else if(src.id() == ID_signed)
  {
    // Might have subtype
    auto &subtype = to_type_with_subtype(src).subtype();
    if(subtype.is_nil())
    {
      // one bit, signed
      return signedbv_typet{1}.with_source_location(source_location);
    }
    else
    {
      // recurse, and make that signed
      auto rec = elaborate_type(subtype);

      if(rec.id() == ID_unsignedbv)
      {
        typet dest = signedbv_typet{to_unsignedbv_type(rec).width()};

        auto verilog_type = rec.get(ID_C_verilog_type);
        if(verilog_type != irep_idt{})
          dest.set(ID_C_verilog_type, verilog_type);

        return dest;
      }
      else if(rec.id() == ID_bool)
        return signedbv_typet{1};
      else
        return rec;
    }
  }
  else if(src.id() == ID_unsigned)
  {
    // Might have subtype
    auto &subtype = to_type_with_subtype(src).subtype();
    if(subtype.is_nil())
    {
      // one bit, unsigned
      return unsignedbv_typet{1}.with_source_location(source_location);
    }
    else
    {
      // recurse, and make that unsigned
      auto rec = elaborate_type(subtype);

      if(rec.id() == ID_signedbv)
      {
        typet dest = unsignedbv_typet{to_signedbv_type(rec).width()};

        auto verilog_type = rec.get(ID_C_verilog_type);
        if(verilog_type != irep_idt{})
          dest.set(ID_C_verilog_type, verilog_type);

        return dest;
      }
      else
        return rec;
    }
  }
  else if(src.id() == ID_verilog_associative_array)
  {
    // The subtype is the element type.
    auto tmp = to_type_with_subtype(src);
    tmp.subtype() = elaborate_type(tmp.subtype());
    return std::move(tmp);
  }
  else if(src.id() == ID_verilog_byte)
  {
    return verilog_byte_typet{}.lower().with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_shortint)
  {
    return verilog_shortint_typet{}.lower().with_source_location(
      source_location);
  }
  else if(src.id() == ID_verilog_int)
  {
    return verilog_int_typet{}.lower().with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_longint)
  {
    return verilog_longint_typet{}.lower().with_source_location(
      source_location);
  }
  else if(src.id() == ID_verilog_integer)
  {
    // four-valued type, signed
    return signedbv_typet{32}.with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_time)
  {
    return unsignedbv_typet{64}.with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_bit)
  {
    // two-valued type
    return bool_typet().with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_logic)
  {
    // two-valued type
    return unsignedbv_typet{1}.with_source_location(source_location);
  }
  else if(src.id() == ID_wire)
  {
    // four-valued type
    return bool_typet().with_source_location(source_location);
  }
  else if(src.id() == ID_verilog_reg)
  {
    // four-valued type
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

    auto identifier = to_verilog_typedef_type(src).identifier();

    if(ns.lookup(identifier, symbol_ptr))
      throw errort().with_location(source_location)
        << "type symbol " << identifier << " not found";

    DATA_INVARIANT(symbol_ptr->is_type, "typedef symbols must be types");

    // elaborate that typedef symbol, recursively, if needed
    elaborate_symbol_rec(identifier);

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
  else if(src.id() == ID_verilog_event)
  {
    return src;
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
      auto &type = declaration_expr.type();

      // Convert the declarators
      for(auto &declarator_expr : declaration_expr.operands())
      {
        auto &declarator =
          static_cast<const verilog_declaratort &>(declarator_expr);

        // merge the types, and elaborate
        auto merged_type = elaborate_type(declarator.merged_type(type));

        struct_union_typet::componentt component;
        component.type() = std::move(merged_type);
        component.add_source_location() = declarator.source_location();
        component.set_base_name(declarator.base_name());
        component.set_name(declarator.base_name());
        components.push_back(std::move(component));
      }
    }

    auto result =
      struct_union_typet{src.id(), std::move(components)}.with_source_location(
        src.source_location());

    if(src.get_bool(ID_packed))
      result.set(ID_packed, true);

    return result;
  }
  else if(src.id() == ID_verilog_string)
  {
    return src;
  }
  else if(src.id() == ID_type)
  {
    return src;
  }
  else if(src.id() == ID_verilog_void)
  {
    return src;
  }
  else if(src.id() == ID_verilog_chandle)
  {
    return src;
  }
  else if(src.id() == ID_verilog_class_type)
  {
    return src;
  }
  else if(src.id() == ID_verilog_package_scope)
  {
    // package::typedef
    return elaborate_package_scope_typedef(to_verilog_package_scope_type(src));
  }
  else if(src.id() == ID_verilog_queue)
  {
    // The subtype is the element type.
    auto tmp = to_type_with_subtype(src);
    tmp.subtype() = elaborate_type(tmp.subtype());
    return std::move(tmp);
  }
  else if(src.id() == ID_const)
  {
    auto tmp = to_type_with_subtype(src).subtype();
    tmp = elaborate_type(tmp);
    tmp.set(ID_C_const, true);
    return tmp;
  }
  else
  {
    throw errort().with_location(source_location)
      << "unexpected type: `" << src.id() << "'";
  }
}
