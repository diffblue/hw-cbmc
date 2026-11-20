/*******************************************************************\

Module: Verilog Lowering

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_lowering.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/expr_identity_map.h>
#include <util/expr_util.h>
#include <util/floatbv_expr.h>
#include <util/ieee_float.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include "aval_bval_encoding.h"
#include "convert_literals.h"
#include "verilog_bits.h"
#include "verilog_expr.h"
#include "verilog_initializer.h"
#include "verilog_layout.h"
#include "verilog_types.h"

#include <algorithm>
#include <optional>
#include <utility>

/// The type of the lowered representation of a variable or net of the
/// given Verilog type, which is also the type of lowered expressions
/// that are not operands of operators, e.g. symbols and array elements:
/// * the three Verilog real types become floatbv;
/// * Verilog integer becomes signedbv[32];
/// * four-valued vector types are modelled two-valued, as unsignedbv or
///   signedbv of the same width; the x/z values are dropped. An unsigned
///   single bit without a declared range becomes bool (make_two_valued).
///   Aggregate types are lowered member-wise.
/// * chandle and event become their encoding.
/// * enums become the lowered base type, see
///   verilog_enum_typet::annotated_base_type.
/// Four-valued values that do contain x/z, e.g. literals, are lowered to
/// the aval/bval encoding, see aval_bval_encoding.h.
typet verilog_lowering(typet type)
{
  if(type.id() == ID_verilog_enum)
  {
    auto &enum_type = to_verilog_enum_type(type);
    auto result = verilog_lowering(enum_type.base_type());
    result.set(ID_C_verilog_type, ID_verilog_enum);
    result.set(ID_C_identifier, enum_type.identifier());
    return result;
  }
  else if(type.id() == ID_verilog_real || type.id() == ID_verilog_realtime)
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
    type.id() == ID_verilog_signedbv || type.id() == ID_verilog_unsignedbv ||
    type.id() == ID_unsignedbv || type.id() == ID_array ||
    type.id() == ID_struct || type.id() == ID_union)
  {
    return make_two_valued(type);
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

void verilog_lower_symbol_types(symbol_table_baset &symbol_table)
{
  for(auto it = symbol_table.begin(); it != symbol_table.end(); it++)
  {
    const auto &symbol = it->second;

    if(symbol.mode != ID_Verilog || symbol.is_type)
      continue;

    if(symbol.is_macro)
    {
      // Parameters are substituted by their value. The back-ends may
      // still enumerate them, e.g. to show their values in traces, and
      // hence enum names and parameters of enum type are lowered,
      // including their value.
      if(symbol.type.id() == ID_verilog_enum)
      {
        auto &writeable_symbol = it.get_writeable_symbol();
        writeable_symbol.type = verilog_lowering(writeable_symbol.type);
        if(writeable_symbol.value.is_not_nil())
        {
          auto lowered_value = verilog_lowering(writeable_symbol.value);

          // A value with x/z keeps its Verilog encoding, as the
          // aval/bval encoding cannot be shown.
          if(is_aval_bval(lowered_value))
          {
            auto &value_type = writeable_symbol.value.type();
            if(value_type.id() == ID_verilog_enum)
              value_type =
                to_verilog_enum_type(value_type).annotated_base_type();
          }
          else
            writeable_symbol.value = std::move(lowered_value);
        }
      }

      continue;
    }

    auto &type = symbol.type;

    if(type.id() == ID_verilog_enum)
    {
      // The lowered type of the base type retains the annotations
      // that identify the enum, e.g. for showing values in traces.
      it.get_writeable_symbol().type = verilog_lowering(type);
    }
    else if(
      type.id() == ID_verilog_real || type.id() == ID_verilog_shortreal ||
      type.id() == ID_verilog_realtime || type.id() == ID_verilog_chandle ||
      type.id() == ID_verilog_event)
    {
      // Remember the Verilog type, e.g. for showing values in traces.
      auto lowered = verilog_lowering(type);
      lowered.set(ID_C_verilog_type, type.id());
      it.get_writeable_symbol().type = std::move(lowered);
    }
    else if(
      type.id() == ID_verilog_unsignedbv || type.id() == ID_verilog_signedbv ||
      type.id() == ID_unsignedbv || type.id() == ID_array ||
      type.id() == ID_struct || type.id() == ID_union)
    {
      // The two-valued modelling retains the attributes of the type,
      // e.g. the Verilog type and the declared range.
      it.get_writeable_symbol().type = verilog_lowering(type);
    }
  }

  // The ports of a module carry the types of the port symbols; use the
  // lowered types.
  for(auto it = symbol_table.begin(); it != symbol_table.end(); it++)
  {
    const auto &symbol = it->second;

    if(symbol.mode != ID_Verilog || symbol.type.id() != ID_module)
      continue;

    auto &ports = to_module_type(it.get_writeable_symbol().type).ports();

    for(auto &port : ports)
    {
      auto port_symbol = symbol_table.lookup(port.identifier());
      if(port_symbol != nullptr)
        port.type() = port_symbol->type;
    }
  }
}

exprt extract(
  const exprt &src,
  const mp_integer &offset,
  const typet &dest_type)
{
  if(src.type().id() == ID_bool)
  {
    // turn into bitvector of size 1
    return extract(typecast_exprt{src, unsignedbv_typet{1}}, offset, dest_type);
  }

  PRECONDITION(src.type().id() != ID_array);
  PRECONDITION(src.type().id() != ID_struct);
  PRECONDITION(src.type().id() != ID_union);

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

/// Like verilog_bits_opt, but also gives the width of a bv_typet.
/// verilog_bits_opt gives no width for bv_typet, as it is not a Verilog
/// type. But to_bitvector converts a packed struct, union or array into
/// a value of type bv_typet, e.g., the concatenation of the members.
static std::optional<mp_integer> bitvector_bits_opt(const typet &type)
{
  if(type.id() == ID_bv)
    return to_bv_type(type).get_width();
  else
    return verilog_bits_opt(type);
}

exprt from_bitvector(
  const exprt &src,
  const mp_integer &offset,
  const typet &dest)
{
  // Take the bits from the part of the source that holds them, rather
  // than extracting each member or element from the entire source.
  // When the source is, e.g., the concatenation of the values of the
  // elements of an array, each element is then taken from its operand,
  // rather than from all of them.
  {
    const auto dest_width_opt = verilog_bits_opt(dest);
    const auto src_width_opt = bitvector_bits_opt(src.type());
    const mp_integer dest_width = dest_width_opt.value_or(0);

    // the operands, if all their widths are known
    bool operand_widths_known =
      src.id() == ID_concatenation && src_width_opt.has_value() &&
      std::all_of(
        src.operands().begin(),
        src.operands().end(),
        [](const exprt &op)
        { return bitvector_bits_opt(op.type()).has_value(); });

    if(operand_widths_known && dest_width != 0)
    {
      // the operands are most significant first
      mp_integer op_lower = *src_width_opt;

      for(auto &op : src.operands())
      {
        auto op_width = *bitvector_bits_opt(op.type());
        op_lower -= op_width;

        if(op_lower <= offset && offset + dest_width <= op_lower + op_width)
        {
          // the operand already has the requested type and width;
          // full_eq, as == ignores the direction and offset of ranges
          if(offset == op_lower && op.type().full_eq(dest))
            return op;

          auto &op_type = op.type();
          bool op_is_aggregate = op_type.id() == ID_struct ||
                                 op_type.id() == ID_union ||
                                 op_type.id() == ID_array;
          return from_bitvector( // rec. call
            op_is_aggregate ? to_bitvector(op) : op,
            offset - op_lower,
            dest);
        }
      }
    }
    else if(
      src.id() == ID_extractbits && dest_width != 0 &&
      src_width_opt.has_value() && offset + dest_width <= *src_width_opt)
    {
      // Only when the bits are within the extract; bits beyond it are
      // zero padding, not the bits of the source above the extract.
      auto index_opt =
        numeric_cast<mp_integer>(to_extractbits_expr(src).index());
      if(index_opt.has_value())
      {
        return from_bitvector( // rec. call
          to_extractbits_expr(src).src(),
          offset + *index_opt,
          dest);
      }
    }
    else if(src.id() == ID_if && dest_width != 0)
    {
      auto &if_expr = to_if_expr(src);
      auto true_value =
        from_bitvector(if_expr.true_case(), offset, dest); // rec. call
      auto false_value =
        from_bitvector(if_expr.false_case(), offset, dest); // rec. call
      return if_exprt{if_expr.cond(), true_value, false_value, dest};
    }
  }

  if(dest.id() == ID_struct)
  {
    const auto &struct_type = to_struct_type(dest);
    exprt::operandst field_values;
    field_values.reserve(struct_type.components().size());

    auto lower_bits = verilog_struct_component_lower_bits(dest);

    for(std::size_t i = 0; i < lower_bits.size(); i++)
    {
      // rec. call
      field_values.push_back(from_bitvector(
        src, offset + lower_bits[i], struct_type.components()[i].type()));
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
  else if(dest.id() == ID_array)
  {
    const auto &array_type = to_array_type(dest);
    auto &element_type = array_type.element_type();
    auto size_int =
      numeric_cast_v<std::size_t>(to_constant_expr(array_type.size()));
    exprt::operandst element_values;
    element_values.reserve(size_int);

    // For packed arrays, we take the index direction into account.
    for(std::size_t index = 0; index < size_int; index++)
    {
      auto element_value = from_bitvector( // rec. call
        src,
        offset + verilog_array_element_lower_bit(array_type, index),
        element_type);
      element_values.push_back(std::move(element_value));
    }

    return array_exprt{std::move(element_values), array_type};
  }
  else
  {
    return extract(src, offset, dest);
  }
}

/// If \p bits is the concatenation (most significant first) of extracts
/// of consecutive, adjacent ranges of one and the same source expression,
/// returns the extract of the combined range; otherwise nullopt.
static std::optional<exprt>
merge_adjacent_extracts(const exprt::operandst &bits, const typet &result_type)
{
  if(bits.empty())
    return {};

  // the source and the bit range of each operand
  std::optional<exprt> source;
  std::optional<mp_integer> top, bottom;

  for(auto &op : bits)
  {
    exprt op_source;
    mp_integer op_low, op_high;

    if(op.id() == ID_extractbits)
    {
      auto &extract = to_extractbits_expr(op);
      auto index_opt = numeric_cast<mp_integer>(extract.index());
      if(!index_opt.has_value())
        return {};
      op_source = extract.src();
      op_low = *index_opt;
      op_high = op_low + to_bitvector_type(op.type()).get_width() - 1;
    }
    else if(op.id() == ID_extractbit)
    {
      auto &extract = to_extractbit_expr(op);
      auto index_opt = numeric_cast<mp_integer>(extract.index());
      if(!index_opt.has_value())
        return {};
      op_source = extract.src();
      op_low = op_high = *index_opt;
    }
    else
      return {};

    if(!source.has_value())
    {
      source = op_source;
      top = op_high;
      bottom = op_low;
    }
    else
    {
      // most significant first: this operand must be directly below
      if(op_source != *source || op_high + 1 != *bottom)
        return {};
      bottom = op_low;
    }
  }

  auto width = *top - *bottom + 1;
  if(width != to_bitvector_type(result_type).get_width())
    return {};

  // The whole source? The source is a bit-vector of some kind (bv,
  // unsignedbv, ...); the result is given the requested type.
  if(
    *bottom == 0 && source->type().id() != ID_bool &&
    can_cast_type<bitvector_typet>(source->type()) &&
    to_bitvector_type(source->type()).get_width() == width)
  {
    if(source->type() == result_type)
      return *source;
    else
      return typecast_exprt{*source, result_type};
  }

  return extractbits_exprt{
    *source, from_integer(*bottom, integer_typet{}), result_type};
}

exprt to_bitvector(const exprt &src)
{
  const auto &src_type = src.type();

  if(
    src_type.id() == ID_struct || src_type.id() == ID_union ||
    src_type.id() == ID_array)
  {
    // Reversing a conversion: the flattening of a value that was itself
    // built from a bit-vector yields that bit-vector.
    if(src.id() == ID_typecast)
    {
      auto &op = to_typecast_expr(src).op();
      if(
        (op.type().id() == ID_unsignedbv || op.type().id() == ID_signedbv ||
         op.type().id() == ID_bv) &&
        to_bitvector_type(op.type()).get_width() == verilog_bits(src_type))
      {
        return op;
      }
    }

    // A conditional: flatten the branches, rather than selecting each
    // member or element from the conditional, which would replicate the
    // conditional once per member or element.
    if(src.id() == ID_if)
    {
      auto &if_expr = to_if_expr(src);
      auto true_bv = to_bitvector(if_expr.true_case());
      auto false_bv = to_bitvector(if_expr.false_case());
      auto type = true_bv.type();
      return if_exprt{
        if_expr.cond(),
        std::move(true_bv),
        typecast_exprt::conditional_cast(std::move(false_bv), type),
        type};
    }
  }

  if(src_type.id() == ID_struct)
  {
    const auto &struct_type = to_struct_type(src_type);
    exprt::operandst field_values;
    field_values.reserve(struct_type.components().size());

    // the first struct member is the most significant
    if(src.id() == ID_struct)
    {
      // A struct constructor: use its operands, rather than member
      // expressions on the constructor, which would replicate the entire
      // constructor once per member.
      auto &operands = src.operands();
      DATA_INVARIANT(
        operands.size() == struct_type.components().size(),
        "struct constructor must have one operand per component");
      for(auto &operand : operands)
        field_values.push_back(to_bitvector(operand)); // rec. call
    }
    else
    {
      for(auto &component : struct_type.components())
      {
        auto member = member_exprt{src, component};
        auto field_value = to_bitvector(member); // rec. call
        field_values.push_back(std::move(field_value));
      }
    }

    auto width_int = numeric_cast_v<std::size_t>(verilog_bits(src));

    // A struct that was built from a bit-vector (from_bitvector) flattens
    // back to that bit-vector.
    if(auto merged = merge_adjacent_extracts(field_values, bv_typet{width_int}))
      return *merged;

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
  else if(src_type.id() == ID_array)
  {
    const auto &array_type = to_array_type(src_type);
    auto size_int =
      numeric_cast_v<std::size_t>(to_constant_expr(array_type.size()));
    exprt::operandst element_values;
    element_values.reserve(size_int);

    // For packed arrays, we take the index direction into account.
    // Concatenation puts the most significant first.
    bool element_zero_first = verilog_array_element_zero_is_msb(array_type);

    // An array constructor: use its operands, rather than index
    // expressions on the constructor, which would replicate the entire
    // constructor once per element.
    auto element = [&src](std::size_t index) -> exprt
    {
      if(src.id() == ID_array)
      {
        DATA_INVARIANT(
          index < src.operands().size(),
          "array constructor must have one operand per element");
        return src.operands()[index];
      }
      else
        return index_exprt{src, from_integer(index, integer_typet{})};
    };

    if(element_zero_first)
    {
      for(std::size_t index = 0; index < size_int; index++)
        element_values.push_back(to_bitvector(element(index))); // rec. call
    }
    else
    {
      for(std::size_t index = size_int; index > 0; index--)
        element_values.push_back(to_bitvector(element(index - 1))); // rec.
    }

    auto width_int = numeric_cast_v<std::size_t>(verilog_bits(src));

    // An array that was built from a bit-vector (from_bitvector) flattens
    // back to that bit-vector.
    if(
      auto merged =
        merge_adjacent_extracts(element_values, bv_typet{width_int}))
      return *merged;

    return concatenation_exprt{std::move(element_values), bv_typet{width_int}};
  }
  else
  {
    return src;
  }
}

exprt verilog_lowering_system_function(const function_call_exprt &call)
{
  auto base_name = to_verilog_identifier_expr(call.function()).base_name();
  auto &arguments = call.arguments();

  if(base_name == "$signed" || base_name == "$unsigned")
  {
    DATA_INVARIANT(
      arguments.size() == 1, id2string(base_name) + " takes one argument");

    if(is_aval_bval(arguments[0]))
    {
      // Change the signedness annotation in the aval/bval type.
      auto result = arguments[0];
      result.type().set(
        ID_C_verilog_aval_bval,
        base_name == "$signed" ? ID_verilog_signedbv : ID_verilog_unsignedbv);
      return result;
    }
    else
    {
      // lower to typecast
      return typecast_exprt{arguments[0], two_valued_vector_type(call.type())};
    }
  }
  else if(base_name == "$value$plusargs" || base_name == "$test$plusargs")
  {
    // IEEE 1800-2017 21.6. EBMC has no command-line plusargs; the
    // functions hence return 0, indicating that the plusarg is not found,
    // and $value$plusargs leaves its variable unchanged.
    return from_integer(0, verilog_lowering(call.type()))
      .with_source_location(call);
  }
  else if(base_name == "$rtoi")
  {
    DATA_INVARIANT(
      arguments.size(), id2string(base_name) + " takes one argument");
    // These truncate, and do not round.
    return floatbv_typecast_exprt{
      arguments[0],
      ieee_floatt::rounding_mode_expr(
        ieee_floatt::rounding_modet::ROUND_TO_ZERO),
      verilog_lowering(call.type())};
  }
  else if(base_name == "$itor")
  {
    DATA_INVARIANT(
      arguments.size(), id2string(base_name) + " takes one argument");
    // No rounding required, any 32-bit integer will fit into double.
    return floatbv_typecast_exprt{
      arguments[0],
      ieee_floatt::rounding_mode_expr(
        ieee_floatt::rounding_modet::ROUND_TO_ZERO),
      verilog_lowering(call.type())};
  }
  else if(base_name == "$bitstoreal")
  {
    DATA_INVARIANT(
      arguments.size(), id2string(base_name) + " takes one argument");
    // not a conversion -- this returns the given bit-pattern as a real
    return typecast_exprt{
      zero_extend_exprt{arguments[0], bv_typet{64}},
      verilog_lowering(call.type())};
  }
  else if(base_name == "$bitstoshortreal")
  {
    DATA_INVARIANT(
      arguments.size(), id2string(base_name) + " takes one argument");
    // not a conversion -- this returns the given bit-pattern as a real
    return typecast_exprt{
      zero_extend_exprt{arguments[0], bv_typet{32}},
      verilog_lowering(call.type())};
  }
  else if(base_name == "$realtobits")
  {
    DATA_INVARIANT(
      arguments.size(), id2string(base_name) + " takes one argument");
    // not a conversion -- this returns the given floating-point bit-pattern as [63:0]
    return zero_extend_exprt{
      typecast_exprt{arguments[0], bv_typet{64}}, call.type()};
  }
  else if(base_name == "$shortrealtobits")
  {
    DATA_INVARIANT(
      arguments.size(), id2string(base_name) + " takes one argument");
    // not a conversion -- this returns the given floating-point bit-pattern as [31:0]
    return zero_extend_exprt{
      typecast_exprt{arguments[0], bv_typet{32}}, call.type()};
  }
  else
  {
    // Left for later, e.g. $past; the type is lowered.
    auto result = call;
    result.type() = verilog_lowering(call.type());
    return std::move(result);
  }
}

exprt verilog_lowering_cast(typecast_exprt expr)
{
  // The operand is lowered already; the type is the Verilog type.
  auto &src_type = expr.op().type();
  auto &dest_type = expr.type();

  if(src_type.id() == ID_verilog_null && dest_type.id() == ID_verilog_chandle)
  {
    return to_verilog_chandle_type(dest_type).null_expr();
  }

  if(src_type.id() == ID_verilog_null && dest_type.id() == ID_verilog_event)
  {
    return to_verilog_event_type(dest_type).null_expr();
  }

  // float to int
  if(
    (src_type.id() == ID_verilog_real ||
     src_type.id() == ID_verilog_shortreal ||
     src_type.id() == ID_verilog_realtime || src_type.id() == ID_floatbv) &&
    (dest_type.id() == ID_signedbv || dest_type.id() == ID_unsignedbv ||
     dest_type.id() == ID_bool || is_four_valued(dest_type)))
  {
    // 1800-2017 6.12.2 requires rounding away from zero when converting
    // to integers.
    auto rm = floatbv_rounding_mode(ieee_floatt::rounding_modet::ROUND_TO_AWAY);
    auto rti =
      floatbv_round_to_integral_exprt{expr.op(), rm}.with_source_location(
        expr.source_location());
    auto new_cast = floatbv_typecast_exprt{
      rti,
      ieee_floatt::rounding_mode_expr(
        ieee_floatt::rounding_modet::ROUND_TO_ZERO),
      two_valued_vector_type(dest_type)};
    return std::move(new_cast);
  }

  // float to float, int to float
  if(
    dest_type.id() == ID_verilog_real ||
    dest_type.id() == ID_verilog_shortreal ||
    dest_type.id() == ID_verilog_realtime)
  {
    // The standard does not say how to round double precision
    // to single precision floating-point.  It does not say how
    // to round integers to float.  We simply use RNA,
    // given the explicit requirement to use RNA when converting
    // float to integer.
    expr.type() = verilog_lowering(dest_type);
    auto new_cast = floatbv_typecast_exprt{
      expr.op(),
      ieee_floatt::rounding_mode_expr(
        ieee_floatt::rounding_modet::ROUND_TO_AWAY),
      verilog_lowering(dest_type)};
    return std::move(new_cast);
  }

  if(is_aval_bval(src_type))
  {
    // When casting a four-valued scalar to bool,
    // 'true' is defined as a "nonzero known value" (1800-2017 12.4).
    if(
      dest_type.id() == ID_bool || dest_type.id() == ID_unsignedbv ||
      dest_type.id() == ID_signedbv || is_four_valued(dest_type))
    {
      return aval_bval(expr);
    }
    else
    {
      // e.g. to an aggregate: use the aval
      expr.op() = aval_underlying(expr.op());
    }
  }

  if(is_four_valued(dest_type))
  {
    // The operand is two-valued, and so is the result, which gets the
    // type of the two-valued modelling of the four-valued type.
    auto two_valued_dest_type = verilog_lowering(dest_type);

    if(
      src_type.id() == ID_struct || src_type.id() == ID_union ||
      src_type.id() == ID_array)
    {
      return extract(to_bitvector(expr.op()), 0, two_valued_dest_type);
    }
    else if(
      two_valued_dest_type.id() == ID_bool && src_type.id() != ID_bool &&
      verilog_bits_opt(src_type).value_or(1) != 1)
    {
      // A cast to a single bit truncates (1800-2017 10.7), unlike a cast
      // to bool.
      return extractbit_exprt{expr.op(), from_integer(0, integer_typet{})};
    }
    else
      return typecast_exprt::conditional_cast(expr.op(), two_valued_dest_type);
  }
  else if(
    dest_type.id() == ID_struct || dest_type.id() == ID_union ||
    dest_type.id() == ID_array)
  {
    auto lowered_dest_type = verilog_lowering(dest_type);

    // from_bitvector requires a bit-vector source; a packed aggregate
    // operand must be flattened first (1800-2017 7.2.1/7.4.1).
    if(
      src_type.id() == ID_struct || src_type.id() == ID_union ||
      src_type.id() == ID_array)
    {
      return from_bitvector(to_bitvector(expr.op()), 0, lowered_dest_type);
    }
    else
      return from_bitvector(expr.op(), 0, lowered_dest_type);
  }
  else
  {
    if(
      src_type.id() == ID_struct || src_type.id() == ID_union ||
      src_type.id() == ID_array)
    {
      return extract(to_bitvector(expr.op()), 0, dest_type);
    }
  }

  // A cast that does not change the (lowered) type is dropped, and so is
  // a cast that undoes a cast of the same width.
  return typecast_exprt::conditional_cast(expr.op(), dest_type);
}

/// The elements lsb..msb (declared indices) of the packed array \p src,
/// as a packed array of type \p result_type. The source is flattened to a
/// bit vector, and the selected sub-array is reconstructed from it.
static exprt lower_packed_array_slice(
  const exprt &src,
  const mp_integer &lsb,
  const mp_integer &msb,
  const typet &result_type)
{
  auto &src_array_type = to_verilog_array_type(src.type());
  auto &result_array_type = to_verilog_array_type(result_type);

  // Flatten the source packed array to a bit vector.
  auto bv = to_bitvector(src);

  // Lowest internal bit of the selected sub-array, see verilog_layout.h.
  auto offset_in_bv = verilog_packed_array_lower_bit(src_array_type, lsb, msb);

  return from_bitvector(bv, offset_in_bv, result_array_type);
}

/// Lower a slice (part-select) of an unpacked array to a fresh array built
/// from element accesses into the source (1800-2017 7.4.3, 7.4.6). The
/// declared indices lsb..msb (with msb>=lsb) select the elements; the
/// result follows the declared range direction of the source, i.e. the
/// element order of the slice matches that of the source. The source is
/// already lowered to an array type.
static exprt lower_unpacked_array_slice(
  const exprt &src,
  const verilog_array_typet &src_array_type,
  const mp_integer &lsb,
  const mp_integer &msb,
  const typet &result_type)
{
  auto &element_type = src_array_type.element_type();
  auto index_type = src_array_type.index_type();
  auto slice_size = msb - lsb + 1;

  // The result array type. Using the Verilog array type of the slice (as
  // produced by the type checker) ensures that the result has the same
  // type as other values of the same declared unpacked array type after
  // lowering, so that e.g. an equality comparison type-checks downstream.
  // The generic lowering pass does not rewrite an array_exprt's type, so
  // the type must be set here exactly as the comparison counterpart.
  typet result_array_type = result_type;

  // Internal element index of a declared index v in the source: elements
  // are stored starting from the left index of the declared range.
  auto src_internal = [&](const mp_integer &v)
  { return verilog_unpacked_array_element_index(src_array_type, v); };

  // The result array stores its elements starting from its own left index.
  // Element j (j=0..slice_size-1) of the result corresponds to the Verilog
  // index lsb+j (increasing) or msb-j (decreasing); both source and result
  // share the same direction.
  exprt::operandst elements;
  elements.reserve(numeric_cast_v<std::size_t>(slice_size));

  for(mp_integer j = 0; j < slice_size; ++j)
  {
    auto v = src_array_type.increasing() ? (lsb + j) : (msb - j);
    auto internal = src_internal(v);
    elements.push_back(
      index_exprt{src, from_integer(internal, index_type), element_type});
  }

  array_exprt result{std::move(elements), to_array_type(result_array_type)};

  return std::move(result);
}

/// true iff the type is one of the Verilog real types
static bool is_verilog_real(const typet &type)
{
  return type.id() == ID_verilog_real || type.id() == ID_verilog_shortreal ||
         type.id() == ID_verilog_realtime;
}

/// Lower +, -, * and / on reals, whose operands are lowered already, to
/// the IEEE 754 operations on floatbv. 1800-2017 6.12 defines the real
/// types as IEEE 754 floating-point, and the standard does not specify a
/// rounding mode for arithmetic; we use the IEEE 754 default,
/// round-to-nearest-even.
static exprt lower_real_arithmetic(const multi_ary_exprt &expr)
{
  auto type = verilog_lowering(expr.type());

  irep_idt id;
  if(expr.id() == ID_plus)
    id = ID_floatbv_plus;
  else if(expr.id() == ID_minus)
    id = ID_floatbv_minus;
  else if(expr.id() == ID_mult)
    id = ID_floatbv_mult;
  else if(expr.id() == ID_div)
    id = ID_floatbv_div;
  else
    PRECONDITION(false);

  auto &operands = expr.operands();
  PRECONDITION(operands.size() >= 2);

  for(auto &op : operands)
  {
    DATA_INVARIANT(
      op.type() == type, "real arithmetic operands must have the result type");
  }

  auto rm =
    ieee_floatt::rounding_mode_expr(ieee_floatt::rounding_modet::ROUND_TO_EVEN);

  // Operators with more than two operands are evaluated left to right.
  exprt result = operands.front();

  for(std::size_t i = 1; i < operands.size(); i++)
    result = ieee_float_op_exprt{result, id, operands[i], rm};

  result.add_source_location() = expr.source_location();

  return result;
}

/// True iff the type is one of the types that a lowered two-valued
/// operand may have.
static bool is_two_valued_vector_or_bool(const typet &type)
{
  return type.id() == ID_bool || type.id() == ID_unsignedbv ||
         type.id() == ID_signedbv;
}

/// The type of a lowered operand of an operator with the given Verilog
/// type, when it is not aval/bval encoded: a four-valued vector type
/// becomes the two-valued vector type of the same width.
static typet two_valued_operand_type(const typet &verilog_type)
{
  if(is_four_valued(verilog_type))
    return two_valued_vector_type(verilog_type);
  else
    return verilog_type;
}

/// Cast the lowered expression \p op to the lowered type \p type, if both
/// are Booleans or two-valued vectors of the same width. A cast that
/// undoes a cast of the same width is dropped.
static exprt coerce_to_type(exprt op, const typet &type)
{
  if(op.type() == type)
    return op;

  if(op.id() == ID_typecast)
  {
    auto &inner = to_typecast_expr(op).op();
    if(
      inner.type() == type && is_two_valued_vector_or_bool(op.type()) &&
      verilog_bits_opt(op.type()) == verilog_bits_opt(type))
    {
      return inner;
    }
  }

  if(
    !is_two_valued_vector_or_bool(type) ||
    (!is_two_valued_vector_or_bool(op.type()) && op.type().id() != ID_bv))
  {
    return op;
  }

  return typecast_exprt::conditional_cast(std::move(op), type);
}

/// The lowering of a symbol of a single-bit type yields a Boolean, and the
/// lowering of an operator yields a vector. The type checker inserts casts
/// between these only when it sees both; it now sees the four-valued
/// vector type on both. Hence, cast the lowered operand \p op to the
/// two-valued type of its Verilog type \p verilog_type, if needed.
static exprt coerce_two_valued(exprt op, const typet &verilog_type)
{
  if(is_aval_bval(op))
    return op;

  auto target = two_valued_operand_type(verilog_type);

  if(!is_two_valued_vector_or_bool(target))
    return op;

  if(!is_two_valued_vector_or_bool(op.type()) && op.type().id() != ID_bv)
    return op;

  if(op.type() == target)
    return op;

  DATA_INVARIANT(
    verilog_bits_opt(op.type()).value_or(0) ==
        verilog_bits_opt(target).value_or(0) ||
      op.type().id() == ID_bv,
    "lowered operand must have the width of its Verilog type");

  return coerce_to_type(std::move(op), target);
}

/// The aval/bval encoding of the lowered operand \p op, whose Verilog type
/// is \p verilog_type.
static exprt to_aval_bval(exprt op, const typet &verilog_type)
{
  if(is_aval_bval(op))
    return op;
  else if(is_four_valued(verilog_type))
  {
    return aval_bval_conversion(
      coerce_two_valued(std::move(op), verilog_type),
      lower_to_aval_bval(verilog_type));
  }
  else
    return op;
}

/// The two-valued constant for the given four-valued constant, which must
/// not contain x/z.
static constant_exprt
two_valued_constant(const constant_exprt &aval_bval_constant, const typet &type)
{
  PRECONDITION(is_four_valued(type));
  PRECONDITION(!aval_bval_has_xz(aval_bval_constant));
  auto width = to_bitvector_type(type).get_width();
  auto aval = bvrep2integer(aval_bval_constant.get_value(), 2 * width, false) %
              power(2, width);
  // interpret as signed if the type is signed
  if(type.id() == ID_verilog_signedbv && aval >= power(2, width - 1))
    aval -= power(2, width);
  return from_integer(aval, two_valued_vector_type(type));
}

using lowering_cachet = expr_identity_mapt<exprt>;

static exprt verilog_lowering_rec(exprt expr, lowering_cachet &cache);

/// Lowers each distinct subexpression once. Expressions in transition
/// relations are DAGs with much sharing; lowering them as trees can take
/// time exponential in their depth.
static exprt verilog_lowering_cached(const exprt &expr, lowering_cachet &cache)
{
  if(auto cached = cache.find(expr))
    return *cached;
  auto result = verilog_lowering_rec(expr, cache);
  cache.insert(expr, result);
  return result;
}

exprt verilog_lowering(exprt expr)
{
  lowering_cachet cache;
  return verilog_lowering_cached(expr, cache);
}

static exprt verilog_lowering_rec(exprt expr, lowering_cachet &cache)
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
      auto base_name = to_verilog_identifier_expr(call.function()).base_name();
      if(base_name == "$bits" || base_name == "$typename")
      {
        // Don't touch.
        // Will be expanded by elaborate_constant_system_function_call,
        // and we want the argument type as is.
        return expr;
      }
    }
  }

  // Enum types are replaced by their annotated base type.
  // The lowering of the expression then proceeds as for the base type.
  if(expr.type().id() == ID_verilog_enum)
    expr.type() = to_verilog_enum_type(expr.type()).annotated_base_type();

  for(auto &op : expr.operands())
  {
    // The test reads the type only. Writing to the operand would unshare
    // it, and the cache of lowered subexpressions is keyed by node.
    if(std::as_const(op).type().id() == ID_verilog_enum)
      op.type() = to_verilog_enum_type(op.type()).annotated_base_type();
  }

  // The Verilog types of the expression and of the operands are needed
  // after lowering the operands. This is a shallow copy.
  const exprt verilog_expr = expr;
  const typet &verilog_type = verilog_expr.type();

  // Do the operands recursively
  for(auto &op : expr.operands())
    op = verilog_lowering_cached(op, cache);

  // Helpers for the operands. The lowering of a four-valued operator is
  // the aval/bval encoding if any of its lowered operands is aval/bval
  // encoded, i.e., may hold x/z. Otherwise, the operator is lowered to the
  // two-valued operator on the two-valued operands.
  auto verilog_operand_type = [&verilog_expr](std::size_t i) -> const typet &
  { return verilog_expr.operands()[i].type(); };

  auto any_aval_bval = [&expr]() -> bool
  {
    return std::any_of(
      expr.operands().begin(),
      expr.operands().end(),
      [](const exprt &op) { return is_aval_bval(op); });
  };

  auto all_bool = [&expr]() -> bool
  {
    return std::all_of(
      expr.operands().begin(),
      expr.operands().end(),
      [](const exprt &op) { return op.type().id() == ID_bool; });
  };

  auto coerce_operands = [&expr, &verilog_operand_type]()
  {
    auto &operands = expr.operands();
    for(std::size_t i = 0; i < operands.size(); i++)
      operands[i] = coerce_two_valued(operands[i], verilog_operand_type(i));
  };

  auto aval_bval_operands = [&expr, &verilog_operand_type]()
  {
    auto &operands = expr.operands();
    for(std::size_t i = 0; i < operands.size(); i++)
      operands[i] = to_aval_bval(operands[i], verilog_operand_type(i));
  };

  // the two-valued form of a four-valued operator on vectors
  auto two_valued_operator = [&expr, &coerce_operands]() -> exprt
  {
    coerce_operands();
    expr.type() = two_valued_vector_type(expr.type());
    return expr;
  };

  // whether the expression is a single bit without declared range
  auto is_single_bit = [&verilog_type]() -> bool
  {
    return is_four_valued(verilog_type) &&
           to_bitvector_type(verilog_type).get_width() == 1 &&
           verilog_type.get(ID_C_offset).empty();
  };

  if(expr.id() == ID_constant)
  {
    auto &constant_expr = to_constant_expr(expr);

    if(is_four_valued(expr.type()))
    {
      // encode into aval/bval
      auto aval_bval_constant = lower_to_aval_bval(constant_expr);

      // A four-valued constant without x/z is two-valued.
      if(aval_bval_has_xz(aval_bval_constant))
        return std::move(aval_bval_constant);
      else
      {
        return two_valued_constant(aval_bval_constant, expr.type())
          .with_source_location(expr.source_location());
      }
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
  else if(
    expr.id() == ID_symbol || expr.id() == ID_nondet_symbol ||
    expr.id() == ID_next_symbol)
  {
    // The symbol table keeps the Verilog type; the symbols in the lowered
    // expressions have the lowered type.
    expr.type() = verilog_lowering(expr.type());
    return expr;
  }
  else if(
    expr.id() == ID_le || expr.id() == ID_ge || expr.id() == ID_lt ||
    expr.id() == ID_gt)
  {
    if(is_four_valued(expr.type()))
    {
      if(any_aval_bval())
      {
        aval_bval_operands();
        return aval_bval(to_binary_relation_expr(expr));
      }
      else
      {
        coerce_operands();
        expr.type() = bool_typet{};
        return expr;
      }
    }
    else
    {
      coerce_operands();
      return expr;
    }
  }
  else if(expr.id() == ID_concatenation)
  {
    if(is_four_valued(expr.type()))
    {
      if(any_aval_bval())
      {
        // The operands that are two-valued must be vectors.
        coerce_operands();
        for(auto &op : expr.operands())
          if(op.type().id() == ID_bool)
            op = typecast_exprt{op, unsignedbv_typet{1}};

        return aval_bval_concatenation(
          to_concatenation_expr(expr).operands(),
          lower_to_aval_bval(expr.type()));
      }
      else
      {
        // Operands of any bit-vector type, and Booleans, may be
        // concatenated.
        expr.type() = two_valued_vector_type(expr.type());
        return expr;
      }
    }

    return expr;
  }
  else if(expr.id() == ID_power)
  {
    auto &power_expr = to_power_expr(expr);

    // encode into aval/bval
    if(is_four_valued(expr.type()) && any_aval_bval())
    {
      aval_bval_operands();
      return aval_bval(power_expr);
    }
    else
    {
      if(is_four_valued(expr.type()))
        two_valued_operator();
      else
        coerce_operands();

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
    // These act like an assignment, and hence, the type checker
    // has already converted the argument to the target type.
    auto &type_cast = to_verilog_explicit_type_cast_expr(expr);
    return coerce_two_valued(type_cast.op(), verilog_type);
  }
  else if(expr.id() == ID_verilog_explicit_signing_cast)
  {
    auto &signing_cast = to_verilog_explicit_signing_cast_expr(expr);
    if(is_aval_bval(signing_cast.op()))
    {
      // Change the signedness annotation in the aval/bval type.
      auto result = signing_cast.op();
      result.type().set(
        ID_C_verilog_aval_bval,
        signing_cast.is_signed() ? ID_verilog_signedbv : ID_verilog_unsignedbv);
      return result;
    }
    else
    {
      return typecast_exprt::conditional_cast(
        signing_cast.op(), two_valued_operand_type(signing_cast.type()));
    }
  }
  else if(expr.id() == ID_verilog_explicit_size_cast)
  {
    // These act like an assignment, and hence, the type checker
    // has already converted the argument to the target type.
    auto &size_cast = to_verilog_explicit_size_cast_expr(expr);
    return coerce_two_valued(size_cast.op(), verilog_type);
  }
  else if(
    expr.id() == ID_verilog_streaming_concatenation_left_to_right ||
    expr.id() == ID_verilog_streaming_concatenation_right_to_left)
  {
    auto &streaming_concatenation =
      to_verilog_streaming_concatenation_expr(expr);

    // The stream expressions are the operands of the braced list, and
    // must be bit-vectors.
    auto &stream_expressions = streaming_concatenation.has_slice_size()
                                 ? expr.operands()[1].operands()
                                 : expr.operands()[0].operands();
    auto &verilog_stream_expressions =
      streaming_concatenation.has_slice_size()
        ? verilog_expr.operands()[1].operands()
        : verilog_expr.operands()[0].operands();

    for(std::size_t i = 0; i < stream_expressions.size(); i++)
    {
      auto &op = stream_expressions[i];
      op = coerce_two_valued(op, verilog_stream_expressions[i].type());
      if(op.type().id() == ID_bool)
        op = typecast_exprt{op, unsignedbv_typet{1}};
    }

    return streaming_concatenation.lower();
  }
  else if(expr.id() == ID_verilog_non_indexed_part_select)
  {
    auto &part_select = to_verilog_non_indexed_part_select_expr(expr);
    auto &src = part_select.src();

    // A non-indexed part-select on a packed array selects a range of
    // ELEMENTS (1800-2017 7.4.5/7.4.6, 11.5.1); the result is itself a
    // packed array. Lower by flattening the source to a bit vector and
    // reconstructing the selected sub-array.
    if(
      src.type().id() == ID_array &&
      src.type().get(ID_C_verilog_type) == ID_verilog_packed_array)
    {
      auto msb = numeric_cast_v<mp_integer>(
        to_constant_expr(part_select.msb())); // declared index, msb>=lsb
      auto lsb =
        numeric_cast_v<mp_integer>(to_constant_expr(part_select.lsb()));

      return lower_packed_array_slice(
        src, lsb, msb, verilog_lowering(part_select.type()));
    }

    // A non-indexed part-select on an unpacked array selects a range of
    // ELEMENTS (1800-2017 7.4.3); the result is itself an unpacked array.
    // Build a fresh array from element accesses into the source, following
    // the declared range direction.
    if(
      src.type().id() == ID_array &&
      src.type().get(ID_C_verilog_type) == ID_verilog_unpacked_array)
    {
      auto &src_array_type = to_verilog_array_type(src.type());

      auto msb = numeric_cast_v<mp_integer>(
        to_constant_expr(part_select.msb())); // declared index, msb>=lsb
      auto lsb =
        numeric_cast_v<mp_integer>(to_constant_expr(part_select.lsb()));

      return lower_unpacked_array_slice(
        src, src_array_type, lsb, msb, verilog_lowering(part_select.type()));
    }

    // The source must be a vector.
    src = coerce_two_valued(src, verilog_operand_type(0));
    if(src.type().id() == ID_bool)
      src = typecast_exprt{src, unsignedbv_typet{1}};

    return part_select.lower();
  }
  else if(
    expr.id() == ID_verilog_indexed_part_select_plus ||
    expr.id() == ID_verilog_indexed_part_select_minus)
  {
    auto &part_select = to_verilog_indexed_part_select_plus_or_minus_expr(expr);
    auto &src = part_select.src();

    // An indexed part-select on a packed array selects a range of
    // ELEMENTS (1800-2017 7.4.6, 11.5.1); the result is itself a packed
    // array.
    if(
      src.type().id() == ID_array &&
      src.type().get(ID_C_verilog_type) == ID_verilog_packed_array)
    {
      // The type checker has rewritten index and width to constants and
      // computed the result type with declared offset lsb.
      auto &result_array_type = to_verilog_array_type(part_select.type());
      auto lsb = result_array_type.offset();
      auto msb = lsb + result_array_type.size_int() - 1;

      return lower_packed_array_slice(
        src, lsb, msb, verilog_lowering(part_select.type()));
    }

    // An indexed part-select on an unpacked array selects a range of
    // ELEMENTS (1800-2017 7.4.6); the result is itself an unpacked array.
    if(
      src.type().id() == ID_array &&
      src.type().get(ID_C_verilog_type) == ID_verilog_unpacked_array)
    {
      auto &src_array_type = to_verilog_array_type(src.type());

      // The type checker has rewritten index and width to constants and
      // computed the result type with declared offset lsb.
      auto &result_array_type = to_verilog_array_type(part_select.type());
      auto lsb = result_array_type.offset();
      auto msb = lsb + result_array_type.size_int() - 1;

      return lower_unpacked_array_slice(
        src, src_array_type, lsb, msb, verilog_lowering(part_select.type()));
    }

    // The source must be a vector, and so must be the index.
    coerce_operands();
    if(src.type().id() == ID_bool)
      src = typecast_exprt{src, unsignedbv_typet{1}};

    return part_select.lower();
  }
  else if(
    expr.id() == ID_verilog_case_equality ||
    expr.id() == ID_verilog_case_inequality)
  {
    // Result is two-valued, comparing x/z as given.
    if(any_aval_bval())
      aval_bval_operands();
    else
      coerce_operands();

    if(expr.id() == ID_verilog_case_equality)
      return to_verilog_case_equality_expr(expr).lower();
    else
      return to_verilog_case_inequality_expr(expr).lower();
  }
  else if(
    expr.id() == ID_verilog_logical_equality ||
    expr.id() == ID_verilog_logical_inequality)
  {
    if(any_aval_bval())
    {
      aval_bval_operands();
      if(expr.id() == ID_verilog_logical_equality)
        return aval_bval(to_verilog_logical_equality_expr(expr));
      else
        return aval_bval(to_verilog_logical_inequality_expr(expr));
    }
    else
    {
      // On two-valued operands, it's the same as proper equality.
      coerce_operands();
      auto &binary_expr = to_binary_expr(expr);
      if(expr.id() == ID_verilog_logical_equality)
        return equal_exprt{binary_expr.lhs(), binary_expr.rhs()};
      else
        return notequal_exprt{binary_expr.lhs(), binary_expr.rhs()};
    }
  }
  else if(expr.id() == ID_verilog_wildcard_equality)
  {
    coerce_operands();
    return aval_bval(to_verilog_wildcard_equality_expr(expr));
  }
  else if(expr.id() == ID_verilog_wildcard_inequality)
  {
    coerce_operands();
    return aval_bval(to_verilog_wildcard_inequality_expr(expr));
  }
  else if(expr.id() == ID_equal || expr.id() == ID_notequal)
  {
    // Equality of two unpacked arrays (1800-2017 7.6, 11.4.5). The
    // operands are already lowered; some backends do not reliably compare
    // array values that are built from element expressions (e.g. array
    // slices), so expand the comparison element-wise into a conjunction of
    // element equalities, which is backend-agnostic.
    auto &binary_expr = to_binary_expr(expr);
    auto &lhs_type = binary_expr.lhs().type();

    if(
      lhs_type.id() == ID_array &&
      lhs_type.get(ID_C_verilog_type) == ID_verilog_unpacked_array &&
      binary_expr.rhs().type() == lhs_type)
    {
      auto &array_type = to_verilog_array_type(lhs_type);
      auto size = array_type.size_int();
      auto index_type = array_type.index_type();
      auto &element_type = array_type.element_type();

      exprt::operandst conjuncts;
      conjuncts.reserve(numeric_cast_v<std::size_t>(size));

      for(mp_integer i = 0; i < size; ++i)
      {
        auto index = from_integer(i, index_type);
        index_exprt lhs_element{binary_expr.lhs(), index, element_type};
        index_exprt rhs_element{binary_expr.rhs(), index, element_type};

        // The element comparison is lowered recursively, so that nested
        // arrays and four-valued element types are handled correctly.
        conjuncts.push_back(verilog_lowering(
          equal_exprt{std::move(lhs_element), std::move(rhs_element)}));
      }

      exprt result = conjunction(conjuncts);

      if(expr.id() == ID_notequal)
        result = not_exprt{std::move(result)};

      return result;
    }

    // The operands must have the same type.
    if(binary_expr.lhs().type() != binary_expr.rhs().type())
    {
      if(any_aval_bval())
        aval_bval_operands();
      else
        coerce_operands();
    }

    return expr; // leave as is
  }
  else if(expr.id() == ID_not)
  {
    auto &not_expr = to_not_expr(expr);

    if(is_four_valued(expr.type()))
    {
      // encode into aval/bval
      if(any_aval_bval())
      {
        aval_bval_operands();
        return aval_bval(not_expr);
      }
      else
      {
        return not_exprt{
          typecast_exprt::conditional_cast(not_expr.op(), bool_typet{})};
      }
    }
    else
      return expr; // leave as is
  }
  else if(expr.id() == ID_bitnot)
  {
    auto &bitnot_expr = to_bitnot_expr(expr);

    if(is_four_valued(expr.type()))
    {
      // encode into aval/bval
      if(any_aval_bval())
      {
        aval_bval_operands();
        return aval_bval(bitnot_expr);
      }
      else if(is_single_bit() && all_bool())
        return not_exprt{bitnot_expr.op()};
      else
        return two_valued_operator();
    }
    else
    {
      coerce_operands();
      return expr; // leave as is
    }
  }
  else if(
    expr.id() == ID_bitand || expr.id() == ID_bitor || expr.id() == ID_bitxor ||
    expr.id() == ID_bitxnor)
  {
    if(is_four_valued(expr.type()) && any_aval_bval())
    {
      // encode into aval/bval
      aval_bval_operands();
      if(expr.id() == ID_bitand)
        return aval_bval_bitand(to_bitand_expr(expr));
      else if(expr.id() == ID_bitor)
        return aval_bval_bitor(to_bitor_expr(expr));
      else
        return aval_bval_xor_xnor(to_multi_ary_expr(expr));
    }
    else if(
      all_bool() && verilog_bits_opt(expr.type()).value_or(0) == 1 &&
      (expr.operands().size() == 2 || expr.id() != ID_bitxnor))
    {
      // Single bits: use the Boolean operators.
      if(expr.id() == ID_bitand)
        return and_exprt{expr.operands()};
      else if(expr.id() == ID_bitor)
        return or_exprt{expr.operands()};
      else if(expr.id() == ID_bitxor)
        return xor_exprt{expr.operands()};
      else // bitxnor
        return equal_exprt{expr.operands()[0], expr.operands()[1]};
    }
    else if(is_four_valued(expr.type()))
      return two_valued_operator();
    else
    {
      coerce_operands();
      return expr; // leave as is
    }
  }
  else if(expr.id() == ID_replication)
  {
    auto &replication_expr = to_replication_expr(expr);

    // encode into aval/bval
    if(is_four_valued(expr.type()))
    {
      if(any_aval_bval())
      {
        aval_bval_operands();
        return aval_bval_replication(replication_expr);
      }
      else
        return two_valued_operator();
    }
    else
    {
      coerce_operands();
      return expr; // leave as is
    }
  }
  else if(
    expr.id() == ID_reduction_or || expr.id() == ID_reduction_and ||
    expr.id() == ID_reduction_nor || expr.id() == ID_reduction_nand ||
    expr.id() == ID_reduction_xor || expr.id() == ID_reduction_xnor)
  {
    // encode into aval/bval
    if(is_four_valued(expr.type()))
    {
      if(any_aval_bval())
      {
        aval_bval_operands();
        return aval_bval_reduction(to_unary_expr(expr));
      }
      else
      {
        coerce_operands();
        expr.type() = bool_typet{};
        return expr;
      }
    }
    else
    {
      coerce_operands();
      return expr; // leave as is
    }
  }
  else if(expr.id() == ID_and || expr.id() == ID_or)
  {
    // Logical && and ||.
    // Four-valued only if the type is four-valued; otherwise the
    // operands are boolean and the expression is left as is.
    if(is_four_valued(expr.type()))
    {
      PRECONDITION(expr.operands().size() == 2);
      if(any_aval_bval())
      {
        aval_bval_operands();
        if(expr.id() == ID_and)
          return aval_bval_logical_and(to_and_expr(expr));
        else
          return aval_bval_logical_or(to_or_expr(expr));
      }
      else
      {
        for(auto &op : expr.operands())
          op = typecast_exprt::conditional_cast(op, bool_typet{});
        expr.type() = bool_typet{};
        return expr;
      }
    }
    else
      return expr; // leave as is
  }
  else if(expr.id() == ID_verilog_iff)
  {
    auto &iff = to_verilog_iff_expr(expr);

    if(is_four_valued(iff.type()) && any_aval_bval())
    {
      // encode into aval/bval
      aval_bval_operands();
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

    if(is_four_valued(implies.type()) && any_aval_bval())
    {
      // encode into aval/bval
      aval_bval_operands();
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
  else if(expr.id() == ID_unary_minus || expr.id() == ID_unary_plus)
  {
    if(is_verilog_real(expr.type()))
    {
      // turn into floatbv
      expr.type() = verilog_lowering(expr.type());
      return expr;
    }
    else if(is_four_valued(expr))
    {
      if(any_aval_bval())
      {
        aval_bval_operands();
        return default_aval_bval_lowering(expr);
      }
      else
        return two_valued_operator();
    }
    else
    {
      coerce_operands();
      return expr;
    }
  }
  else if(expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult)
  {
    if(is_verilog_real(expr.type()))
      return lower_real_arithmetic(to_multi_ary_expr(expr));
    else if(is_four_valued(expr))
    {
      if(any_aval_bval())
      {
        aval_bval_operands();
        return default_aval_bval_lowering(expr);
      }
      else
        return two_valued_operator();
    }
    else
    {
      coerce_operands();
      return expr;
    }
  }
  else if(expr.id() == ID_div || expr.id() == ID_mod)
  {
    if(expr.id() == ID_div && is_verilog_real(expr.type()))
      return lower_real_arithmetic(to_multi_ary_expr(expr));
    else if(is_four_valued(expr))
    {
      // Division by zero yields x (1800-2017 11.4.3), even when the
      // operands are two-valued. This is only encoded when the divisor
      // is a constant zero; otherwise, the two-valued modelling applies.
      // The lowering of the divisor may have cast a constant.
      const exprt *divisor = &to_binary_expr(expr).rhs();
      while(divisor->id() == ID_typecast)
        divisor = &to_typecast_expr(*divisor).op();

      bool divisor_is_zero =
        divisor->is_constant() && !is_aval_bval(*divisor) &&
        numeric_cast<mp_integer>(to_constant_expr(*divisor)) == mp_integer{0};

      if(any_aval_bval() || divisor_is_zero)
      {
        aval_bval_operands();
        return aval_bval_div_mod(to_binary_expr(expr));
      }
      else
        return two_valued_operator();
    }
    else
    {
      coerce_operands();
      return expr;
    }
  }
  else if(expr.id() == ID_lshr || expr.id() == ID_ashr || expr.id() == ID_shl)
  {
    if(is_four_valued(expr.type()))
    {
      if(any_aval_bval())
      {
        // The distance is self-determined, and may be two-valued.
        coerce_operands();
        aval_bval_operands();
        return aval_bval(to_shift_expr(expr));
      }
      else
        return two_valued_operator();
    }
    else
    {
      coerce_operands();
      return expr;
    }
  }
  else if(expr.id() == ID_zero_extend)
  {
    if(is_four_valued(expr.type()))
    {
      if(any_aval_bval())
      {
        aval_bval_operands();
        return aval_bval(to_zero_extend_expr(expr));
      }
      else
        return two_valued_operator();
    }
    else
    {
      coerce_operands();
      return expr;
    }
  }
  else if(expr.id() == ID_verilog_bit_select)
  {
    // This may be an array index or a bit extraction, depending
    // on the type of the first operand.
    auto &bit_select = to_verilog_bit_select_expr(expr);
    auto &src = bit_select.src();

    if(src.type().id() == ID_array)
    {
      // Lower to array index expression
      auto &array_type = to_verilog_array_type(src.type());
      auto index_type = array_type.index_type();

      // A constant index is converted here; it may have a type that is
      // not lowered otherwise, e.g., integer, when generated internally.
      exprt index = typecast_exprt{bit_select.index(), index_type};
      if(bit_select.index().is_constant())
      {
        auto index_int =
          numeric_cast<mp_integer>(to_constant_expr(bit_select.index()));
        if(index_int.has_value())
          index = from_integer(*index_int, index_type);
      }

      if(array_type.is_unpacked())
      {
        // For unpacked arrays, the internal representation stores
        // elements starting from the left index of the range.
        // We need to adjust the Verilog index to the internal index.
        auto array_size = array_type.size_int();
        auto offset = array_type.offset();

        if(array_type.increasing())
        {
          // ascending range [l:r] with l<r, e.g., [0:4]
          // internal index = verilog_index - offset
          if(offset != 0)
            index = minus_exprt{index, from_integer(offset, index_type)};
        }
        else
        {
          // descending range [l:r] with l>=r, e.g., [4:0]
          // internal index = (offset + size - 1) - verilog_index
          index = minus_exprt{
            minus_exprt{
              plus_exprt{
                from_integer(offset, index_type),
                from_integer(array_size, index_type)},
              from_integer(1, index_type)},
            index};
        }

        // Per 1800-2017 7.4.6, reading from an out-of-range index of an
        // unpacked array yields the default value of the element type (0
        // for 2-state types, 'x for 4-state types). The internal index
        // above is computed in the (narrow) index type and may have
        // wrapped around, so the range check below uses the original
        // Verilog index value, which cannot wrap.
        //
        // The index operand has already been lowered; for a four-valued
        // index this is an aval/bval encoding, from which the aval part
        // carries the numeric value.
        auto lowered_index = bit_select.index();
        exprt index_value = is_aval_bval(lowered_index.type())
                              ? aval(lowered_index)
                              : lowered_index;

        auto &element_type = array_type.element_type();

        // Default value of the element type: 'x for a four-valued
        // vector, otherwise the zero/default produced by
        // verilog_default_initializer (0 for 2-state vectors, and the
        // componentwise default for aggregates).
        auto element_default = [&]() -> std::optional<exprt>
        {
          if(
            element_type.id() == ID_verilog_unsignedbv ||
            element_type.id() == ID_verilog_signedbv)
          {
            return to_verilog_unsignedbv_type(element_type).all_x_expr();
          }
          else
            return verilog_default_initializer(element_type);
        };

        // If the index is a compile-time constant, resolve the range
        // check now: emit either the plain access or the default value.
        // This keeps the common constant-index case free of a guard.
        if(index_value.is_constant())
        {
          auto index_int =
            numeric_cast<mp_integer>(to_constant_expr(index_value));
          if(index_int.has_value())
          {
            mp_integer internal = array_type.increasing()
                                    ? (*index_int - offset)
                                    : (offset + array_size - 1 - *index_int);

            if(internal >= 0 && internal < array_size)
              return index_exprt{src, index, element_type};

            auto default_opt = element_default();
            if(default_opt.has_value())
              return std::move(*default_opt);

            // No well-typed default available; fall back to the plain
            // access.
            return index_exprt{src, index, element_type};
          }
        }

        // Perform the range check using the original Verilog index
        // value in a signed bit-vector type that is wide enough to hold
        // both the index value and the array bounds without wrapping
        // around. A fixed-width type is used (rather than unbounded
        // integers) so that the comparison is handled by the bit-vector
        // backend.
        std::size_t index_width =
          can_cast_type<bitvector_typet>(index_value.type())
            ? to_bitvector_type(index_value.type()).get_width()
            : 1;
        auto bound = array_size + (offset < 0 ? -offset : offset);
        std::size_t compare_width = std::max<std::size_t>(
          index_width + 1,
          numeric_cast_v<std::size_t>(address_bits(bound + 1)) + 1);
        signedbv_typet compare_type{compare_width};

        exprt wide_index = typecast_exprt{index_value, compare_type};

        if(array_type.increasing())
        {
          if(offset != 0)
          {
            wide_index =
              minus_exprt{wide_index, from_integer(offset, compare_type)};
          }
        }
        else
        {
          wide_index = minus_exprt{
            from_integer(offset + array_size - 1, compare_type), wide_index};
        }

        auto in_range = and_exprt{
          binary_relation_exprt{
            wide_index, ID_ge, from_integer(0, compare_type)},
          binary_relation_exprt{
            wide_index, ID_lt, from_integer(array_size, compare_type)}};

        // If we cannot construct a well-typed default for the element
        // type, fall back to the plain (unguarded) array access rather
        // than risk an ill-typed expression.
        auto default_value = element_default();
        if(default_value.has_value())
        {
          return if_exprt{
            in_range,
            index_exprt{src, index, element_type},
            std::move(*default_value)};
        }
      }

      return index_exprt{src, index, array_type.element_type()};
    }
    else
    {
      // Lower to extractbit. The source and the index must be vectors.
      coerce_operands();
      if(src.type().id() == ID_bool)
        src = typecast_exprt{src, unsignedbv_typet{1}};

      auto width = verilog_bits(src.type());
      auto offset = to_verilog_vector_type(src.type()).offset();

      auto index = bit_select.index();

      if(index.type().id() == ID_bool)
        index = typecast_exprt{index, unsignedbv_typet{1}};

      if(offset != 0)
        index = minus_exprt{index, from_integer(offset, index.type())};

      if(src.type().get_bool(ID_C_increasing))
        index = minus_exprt{from_integer(width - 1, index.type()), index};

      return extractbit_exprt{src, index};
    }
  }
  else if(expr.id() == ID_member)
  {
    auto &member_expr = to_member_expr(expr);
    auto &compound_type = member_expr.compound().type();

    // Lower member access on packed unions.
    if(compound_type.id() == ID_union)
    {
      auto bv = to_bitvector(member_expr.compound());
      return from_bitvector(bv, 0, verilog_lowering(member_expr.type()));
    }
    else if(compound_type.id() == ID_struct)
    {
      // The member has the type of the component of the lowered compound.
      auto &component = to_struct_type(compound_type)
                          .get_component(member_expr.get_component_name());
      if(component.is_not_nil())
        expr.type() = component.type();
      return expr;
    }
    else
      return expr;
  }
  else if(expr.id() == ID_index)
  {
    // The element has the element type of the lowered array.
    auto &index_expr = to_index_expr(expr);
    if(index_expr.array().type().id() == ID_array)
      expr.type() = to_array_type(index_expr.array().type()).element_type();
    return expr;
  }
  else if(expr.id() == ID_if)
  {
    auto &if_expr = to_if_expr(expr);

    if(is_four_valued(expr.type()) && any_aval_bval())
    {
      aval_bval_operands();
      return aval_bval(if_expr);
    }
    else if(is_verilog_real(expr.type()))
    {
      // The operands are floatbv already; the result must be, too.
      expr.type() = verilog_lowering(expr.type());
      return expr;
    }
    else
    {
      // The condition is Boolean.
      if_expr.cond() =
        typecast_exprt::conditional_cast(if_expr.cond(), bool_typet{});

      // The cases must have the same type.
      if(if_expr.true_case().type() != if_expr.false_case().type())
      {
        if_expr.true_case() =
          coerce_two_valued(if_expr.true_case(), verilog_operand_type(1));
        if_expr.false_case() =
          coerce_two_valued(if_expr.false_case(), verilog_operand_type(2));
      }

      expr.type() = if_expr.true_case().type();
      return expr;
    }
  }
  else if(expr.id() == ID_verilog_unbased_unsized_literal)
  {
    // '0, '1, 'x, 'z
    return verilog_lowering(
      to_verilog_unbased_unsized_literal_expr(expr).expand());
  }
  else if(expr.id() == ID_verilog_based_unsized_literal)
  {
    return verilog_lowering(
      to_verilog_based_unsized_literal_expr(expr).expand());
  }
  else if(expr.id() == ID_struct || expr.id() == ID_array)
  {
    // Aggregate constructors: the operands must have the types of the
    // members of the lowered aggregate type.
    expr.type() = verilog_lowering(expr.type());

    if(expr.id() == ID_struct)
    {
      auto &components = to_struct_type(expr.type()).components();
      auto &operands = expr.operands();
      DATA_INVARIANT(
        components.size() == operands.size(),
        "struct constructor must have one operand per component");
      for(std::size_t i = 0; i < operands.size(); i++)
        operands[i] = coerce_to_type(operands[i], components[i].type());
    }
    else
    {
      auto &element_type = to_array_type(expr.type()).element_type();
      for(auto &op : expr.operands())
        op = coerce_to_type(op, element_type);
    }

    return expr;
  }
  else if(expr.id() == ID_array_of)
  {
    expr.type() = verilog_lowering(expr.type());
    auto &element_type = to_array_type(expr.type()).element_type();
    auto &what = to_array_of_expr(expr).what();
    what = coerce_to_type(what, element_type);
    return expr;
  }
  else if(expr.id() == ID_extractbit || expr.id() == ID_extractbits)
  {
    // The source must be a vector.
    auto &src = to_binary_expr(expr).op0();
    if(src.type().id() == ID_bool)
      src = typecast_exprt{src, unsignedbv_typet{1}};

    if(is_four_valued(expr.type()))
      expr.type() = two_valued_vector_type(expr.type());

    return expr;
  }
  else
  {
    // Leave as is, but lower the type.
    if(
      is_four_valued(expr.type()) || expr.type().id() == ID_array ||
      expr.type().id() == ID_struct || expr.type().id() == ID_union)
    {
      expr.type() = verilog_lowering(expr.type());
    }

    return expr;
  }

  UNREACHABLE;
}
