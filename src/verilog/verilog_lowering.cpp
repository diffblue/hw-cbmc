/*******************************************************************\

Module: Verilog Lowering

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_lowering.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/c_types.h>
#include <util/floatbv_expr.h>
#include <util/ieee_float.h>
#include <util/std_expr.h>

#include "aval_bval_encoding.h"
#include "convert_literals.h"
#include "verilog_bits.h"
#include "verilog_expr.h"
#include "verilog_types.h"

/// Lowers
/// * the three Verilog real types to floatbv;
/// * Verilog integer to signedbv[32]
typet verilog_lowering(typet type)
{
  if(type.id() == ID_verilog_real || type.id() == ID_verilog_realtime)
  {
    return ieee_float_spect::double_precision().to_type();
  }
  else if(type.id() == ID_verilog_shortreal)
  {
    return ieee_float_spect::single_precision().to_type();
  }
  else if(type.id() == ID_verilog_integer)
  {
    return signedbv_typet{32};
  }
  else if(
    type.id() == ID_verilog_signedbv || type.id() == ID_verilog_unsignedbv)
  {
    return lower_to_aval_bval(type);
  }
  else if(type.id() == ID_verilog_chandle)
  {
    return to_verilog_chandle_type(type).encoding();
  }
  else if(type.id() == ID_verilog_event)
  {
    return to_verilog_event_type(type).encoding();
  }
  else
    return type;
}

exprt extract(
  const exprt &src,
  const mp_integer &offset,
  const typet &dest_type)
{
  auto src_width = to_bitvector_type(src.type()).get_width();
  auto dest_width = verilog_bits(dest_type);

  // first add padding, if src is too small
  exprt padded_src;
  auto padding_width = dest_width + offset - src_width;

  if(padding_width > 0)
  {
    auto padded_width_int =
      numeric_cast_v<std::size_t>(src_width + padding_width);
    padded_src = concatenation_exprt{
      {unsignedbv_typet{numeric_cast_v<std::size_t>(padding_width)}.zero_expr(),
       src},
      bv_typet{padded_width_int}};
  }
  else // large enough
    padded_src = src;

  // now extract
  if(dest_type.id() == ID_bool)
  {
    return extractbit_exprt{padded_src, from_integer(offset, integer_typet{})};
  }
  else
  {
    return extractbits_exprt{
      padded_src, from_integer(offset, integer_typet{}), dest_type};
  }
}

exprt from_bitvector(
  const exprt &src,
  const mp_integer &offset,
  const typet &dest)
{
  if(dest.id() == ID_struct)
  {
    const auto &struct_type = to_struct_type(dest);
    exprt::operandst field_values;
    field_values.reserve(struct_type.components().size());

    // start from the top; the first field is the most significant
    mp_integer component_offset = verilog_bits(dest);

    for(auto &component : struct_type.components())
    {
      auto width = verilog_bits(component.type());
      component_offset -= width;
      // rec. call
      field_values.push_back(
        from_bitvector(src, offset + component_offset, component.type()));
    }

    return struct_exprt{std::move(field_values), struct_type};
  }
  else if(dest.id() == ID_union)
  {
    // We use the first field of the union.
    // All fields of a SystemVerilog packed union must have the same width.
    const auto &union_type = to_union_type(dest);
    DATA_INVARIANT(
      !union_type.components().empty(),
      "union type must have at least one field");
    auto &field = union_type.components().front();

    // rec. call
    auto field_value = from_bitvector(src, offset, field.type());

    return union_exprt{field.get_name(), std::move(field_value), union_type};
  }
  else
  {
    return extract(src, offset, dest);
  }
}

exprt to_bitvector(const exprt &src)
{
  const auto &src_type = src.type();

  if(src_type.id() == ID_struct)
  {
    const auto &struct_type = to_struct_type(src_type);
    exprt::operandst field_values;
    field_values.reserve(struct_type.components().size());

    // the first struct member is the most significant
    for(auto &component : struct_type.components())
    {
      auto member = member_exprt{src, component};
      auto field_value = to_bitvector(member); // rec. call
      field_values.push_back(std::move(field_value));
    }

    auto width_int = numeric_cast_v<std::size_t>(verilog_bits(src));
    return concatenation_exprt{std::move(field_values), bv_typet{width_int}};
  }
  else if(src_type.id() == ID_union)
  {
    const auto &union_type = to_union_type(src_type);
    DATA_INVARIANT(
      !union_type.components().empty(),
      "union type must have at least one field");
    auto &field = union_type.components().front();
    auto member = member_exprt{src, field};
    return to_bitvector(member); // rec. call
  }
  else
  {
    return src;
  }
}

exprt verilog_lowering_system_function(const function_call_exprt &call)
{
  auto identifier = to_symbol_expr(call.function()).get_identifier();
  auto &arguments = call.arguments();

  if(identifier == "$signed" || identifier == "$unsigned")
  {
    // lower to typecast
    DATA_INVARIANT(
      arguments.size() == 1, id2string(identifier) + " takes one argument");
    return typecast_exprt{arguments[0], call.type()};
  }
  else if(identifier == "$rtoi")
  {
    DATA_INVARIANT(
      arguments.size(), id2string(identifier) + " takes one argument");
    // These truncate, and do not round.
    return floatbv_typecast_exprt{
      arguments[0],
      ieee_floatt::rounding_mode_expr(
        ieee_floatt::rounding_modet::ROUND_TO_ZERO),
      verilog_lowering(call.type())};
  }
  else if(identifier == "$itor")
  {
    DATA_INVARIANT(
      arguments.size(), id2string(identifier) + " takes one argument");
    // No rounding required, any 32-bit integer will fit into double.
    return floatbv_typecast_exprt{
      arguments[0],
      ieee_floatt::rounding_mode_expr(
        ieee_floatt::rounding_modet::ROUND_TO_ZERO),
      verilog_lowering(call.type())};
  }
  else if(identifier == "$bitstoreal")
  {
    DATA_INVARIANT(
      arguments.size(), id2string(identifier) + " takes one argument");
    // not a conversion -- this returns the given bit-pattern as a real
    return typecast_exprt{
      zero_extend_exprt{arguments[0], bv_typet{64}},
      verilog_lowering(call.type())};
  }
  else if(identifier == "$bitstoshortreal")
  {
    DATA_INVARIANT(
      arguments.size(), id2string(identifier) + " takes one argument");
    // not a conversion -- this returns the given bit-pattern as a real
    return typecast_exprt{
      zero_extend_exprt{arguments[0], bv_typet{32}},
      verilog_lowering(call.type())};
  }
  else if(identifier == "$realtobits")
  {
    DATA_INVARIANT(
      arguments.size(), id2string(identifier) + " takes one argument");
    // not a conversion -- this returns the given floating-point bit-pattern as [63:0]
    return zero_extend_exprt{
      typecast_exprt{arguments[0], bv_typet{64}}, call.type()};
  }
  else if(identifier == "$shortrealtobits")
  {
    DATA_INVARIANT(
      arguments.size(), id2string(identifier) + " takes one argument");
    // not a conversion -- this returns the given floating-point bit-pattern as [31:0]
    return zero_extend_exprt{
      typecast_exprt{arguments[0], bv_typet{32}}, call.type()};
  }
  else
    return call;
}

exprt verilog_lowering_cast(typecast_exprt expr)
{
  auto &src_type = expr.op().type();
  auto &dest_type = expr.type();

  if(
    dest_type.id() == ID_verilog_real ||
    dest_type.id() == ID_verilog_shortreal ||
    dest_type.id() == ID_verilog_realtime || src_type.id() == ID_floatbv)
  {
    // This may require rounding, hence add rounding mode.
    // 1800-2017 6.12.2 requires rounding away from zero,
    // which we don't have.
    expr.type() = verilog_lowering(dest_type);
    auto new_cast = floatbv_typecast_exprt{
      expr.op(),
      ieee_floatt::rounding_mode_expr(
        ieee_floatt::rounding_modet::ROUND_TO_EVEN),
      verilog_lowering(dest_type)};
    return std::move(new_cast);
  }

  if(is_aval_bval(src_type) && dest_type.id() == ID_bool)
  {
    // When casting a four-valued scalar to bool,
    // 'true' is defined as a "nonzero known value" (1800-2017 12.4).
    return aval_bval(expr);
  }
  else
  {
    if(
      dest_type.id() == ID_verilog_unsignedbv ||
      dest_type.id() == ID_verilog_signedbv)
    {
      auto aval_bval_type = lower_to_aval_bval(dest_type);
      return aval_bval_conversion(expr.op(), aval_bval_type);
    }
    else if(dest_type.id() == ID_struct || dest_type.id() == ID_union)
    {
      return from_bitvector(expr.op(), 0, dest_type);
    }
    else
    {
      if(src_type.id() == ID_struct || src_type.id() == ID_union)
      {
        return extract(to_bitvector(expr.op()), 0, dest_type);
      }
    }
  }

  return std::move(expr);
}

exprt verilog_lowering(exprt expr)
{
  // lowered already
  PRECONDITION(expr.id() != ID_floatbv_typecast);

  if(expr.id() == ID_verilog_inside)
  {
    // The lowering uses wildcard equality, which needs to be further lowered
    auto &inside = to_verilog_inside_expr(expr);
    expr = inside.lower();
  }
  else if(expr.id() == ID_function_call)
  {
    auto &call = to_function_call_expr(expr);
    if(call.is_system_function_call())
    {
      auto identifier = to_symbol_expr(call.function()).get_identifier();
      if(identifier == "$typename")
      {
        // Don't touch.
        // Will be expanded by elaborate_constant_system_function_call,
        // and we want the argument type as is.
        return expr;
      }
    }
  }

  // Do the operands recursively
  for(auto &op : expr.operands())
    op = verilog_lowering(op);

  if(expr.id() == ID_constant)
  {
    auto &constant_expr = to_constant_expr(expr);

    if(
      expr.type().id() == ID_verilog_unsignedbv ||
      expr.type().id() == ID_verilog_signedbv)
    {
      // encode into aval/bval
      return lower_to_aval_bval(constant_expr);
    }
    else if(
      expr.type().id() == ID_verilog_real ||
      expr.type().id() == ID_verilog_realtime ||
      expr.type().id() == ID_verilog_shortreal)
    {
      // turn into floatbv -- same encoding,
      // no need to change value
      expr.type() = verilog_lowering(expr.type());
    }
    else if(expr.type().id() == ID_string)
    {
      auto result = convert_string_literal(constant_expr.get_value());
      result.add_source_location() = expr.source_location();
      expr = std::move(result);
    }
    else if(expr.type().id() == ID_verilog_chandle)
    {
      // this is 'null'
      return to_verilog_chandle_type(expr.type()).null_expr();
    }
    else if(expr.type().id() == ID_verilog_event)
    {
      // this is 'null'
      return to_verilog_event_type(expr.type()).null_expr();
    }

    return expr;
  }
  else if(expr.id() == ID_symbol)
  {
    auto &symbol_expr = to_symbol_expr(expr);
    if(expr.type().id() == ID_verilog_chandle)
    {
      auto &chandle_type = to_verilog_chandle_type(expr.type());
      return symbol_exprt{
        symbol_expr.get_identifier(), chandle_type.encoding()};
    }
    else if(expr.type().id() == ID_verilog_event)
    {
      auto &event_type = to_verilog_event_type(expr.type());
      return symbol_exprt{symbol_expr.get_identifier(), event_type.encoding()};
    }
    else
      return expr;
  }
  else if(expr.id() == ID_concatenation)
  {
    if(
      expr.type().id() == ID_verilog_unsignedbv ||
      expr.type().id() == ID_verilog_signedbv)
    {
      return aval_bval_concatenation(
        to_concatenation_expr(expr).operands(),
        lower_to_aval_bval(expr.type()));
    }

    return expr;
  }
  else if(expr.id() == ID_power)
  {
    auto &power_expr = to_power_expr(expr);

    // encode into aval/bval
    if(is_four_valued(expr.type()))
      return aval_bval(power_expr);
    else
    {
      DATA_INVARIANT(
        power_expr.base().type() == power_expr.type(),
        "power expression type consistency");

      auto exponent_int = numeric_cast<std::size_t>(power_expr.exponent());
      if(exponent_int.has_value())
      {
        if(*exponent_int == 0)
          return from_integer(1, expr.type());
        else if(*exponent_int == 1)
          return power_expr.base();
        else // >= 2
        {
          auto factors =
            exprt::operandst{exponent_int.value(), power_expr.base()};
          return mult_exprt{factors, expr.type()};
        }
      }
      else
        return expr;
    }
  }
  else if(expr.id() == ID_typecast)
  {
    return verilog_lowering_cast(to_typecast_expr(expr));
  }
  else if(expr.id() == ID_verilog_explicit_type_cast)
  {
    return verilog_lowering_cast(
      to_typecast_expr(to_verilog_explicit_type_cast_expr(expr).lower()));
  }
  else if(expr.id() == ID_verilog_explicit_signing_cast)
  {
    return to_verilog_explicit_signing_cast_expr(expr).lower();
  }
  else if(expr.id() == ID_verilog_explicit_size_cast)
  {
    return to_verilog_explicit_size_cast_expr(expr).lower();
  }
  else if(
    expr.id() == ID_verilog_streaming_concatenation_left_to_right ||
    expr.id() == ID_verilog_streaming_concatenation_right_to_left)
  {
    auto &streaming_concatenation =
      to_verilog_streaming_concatenation_expr(expr);
    return streaming_concatenation.lower();
  }
  else if(expr.id() == ID_verilog_non_indexed_part_select)
  {
    auto &part_select = to_verilog_non_indexed_part_select_expr(expr);
    return part_select.lower();
  }
  else if(
    expr.id() == ID_verilog_indexed_part_select_plus ||
    expr.id() == ID_verilog_indexed_part_select_minus)
  {
    auto &part_select = to_verilog_indexed_part_select_plus_or_minus_expr(expr);
    return part_select.lower();
  }
  else if(expr.id() == ID_verilog_case_equality)
  {
    // Result is two-valued, comparing x/z as given.
    return to_verilog_case_equality_expr(expr).lower();
  }
  else if(expr.id() == ID_verilog_case_inequality)
  {
    // Result is two-valued, comparing x/z as given.
    return to_verilog_case_inequality_expr(expr).lower();
  }
  else if(expr.id() == ID_verilog_logical_equality)
  {
    return aval_bval(to_verilog_logical_equality_expr(expr));
  }
  else if(expr.id() == ID_verilog_logical_inequality)
  {
    return aval_bval(to_verilog_logical_inequality_expr(expr));
  }
  else if(expr.id() == ID_verilog_wildcard_equality)
  {
    return aval_bval(to_verilog_wildcard_equality_expr(expr));
  }
  else if(expr.id() == ID_verilog_wildcard_inequality)
  {
    return aval_bval(to_verilog_wildcard_inequality_expr(expr));
  }
  else if(expr.id() == ID_not)
  {
    auto &not_expr = to_not_expr(expr);

    // encode into aval/bval
    if(is_four_valued(expr.type()))
      return aval_bval(not_expr);
    else
      return expr; // leave as is
  }
  else if(expr.id() == ID_bitnot)
  {
    auto &bitnot_expr = to_bitnot_expr(expr);

    // encode into aval/bval
    if(is_four_valued(expr.type()))
      return aval_bval(bitnot_expr);
    else
      return expr; // leave as is
  }
  else if(expr.id() == ID_verilog_iff)
  {
    auto &iff = to_verilog_iff_expr(expr);

    if(is_four_valued(iff.type()))
    {
      // encode into aval/bval
      return aval_bval(iff);
    }
    else
    {
      auto lhs_boolean =
        typecast_exprt::conditional_cast(iff.lhs(), bool_typet{});
      auto rhs_boolean =
        typecast_exprt::conditional_cast(iff.rhs(), bool_typet{});
      return equal_exprt{lhs_boolean, rhs_boolean};
    }
  }
  else if(expr.id() == ID_verilog_implies)
  {
    auto &implies = to_verilog_implies_expr(expr);

    if(is_four_valued(implies.type()))
    {
      // encode into aval/bval
      return aval_bval(implies);
    }
    else
    {
      auto lhs_boolean =
        typecast_exprt::conditional_cast(implies.lhs(), bool_typet{});
      auto rhs_boolean =
        typecast_exprt::conditional_cast(implies.rhs(), bool_typet{});
      return implies_exprt{lhs_boolean, rhs_boolean};
    }
  }
  else if(expr.id() == ID_function_call)
  {
    // Is it a 'system function call'?
    auto &call = to_function_call_expr(expr);
    if(call.is_system_function_call())
      return verilog_lowering_system_function(call);
    else
      return expr;
  }
  else if(expr.id() == ID_unary_minus)
  {
    if(
      expr.type().id() == ID_verilog_real ||
      expr.type().id() == ID_verilog_realtime ||
      expr.type().id() == ID_verilog_shortreal)
    {
      // turn into floatbv
      expr.type() = verilog_lowering(expr.type());
    }

    return expr;
  }
  else
    return expr; // leave as is

  UNREACHABLE;
}
