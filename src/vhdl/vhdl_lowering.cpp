/*******************************************************************\

Module: VHDL Lowering

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// VHDL Lowering

#include "vhdl_lowering.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/mathematical_expr.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <ebmc/ebmc_error.h>
#include <verilog/verilog_types.h>

#include "vhdl_expr.h"
#include "vhdl_types.h"

#include <algorithm>

/// true if the lowered type is a bit-vector, i.e., the VHDL type is an
/// array of bit, std_(u)logic or boolean
static bool lowers_to_bitvector(const typet &vhdl_type)
{
  if(vhdl_type.id() != ID_vhdl_array)
    return false;
  auto &array_type = to_vhdl_array_type(vhdl_type);
  return vhdl_lowering(array_type.element_type()).id() == ID_bool;
}

typet vhdl_lowering(const typet &type)
{
  if(type.id() == ID_vhdl_enumeration)
  {
    auto &enumeration_type = to_vhdl_enumeration_type(type);
    auto base = enumeration_type.base_name();

    if(base == "boolean" || base == "bit" || base == "std_ulogic")
      return bool_typet{};

    enumeration_typet result;
    result.elements() = enumeration_type.elements();
    result.add_source_location() = type.source_location();
    return std::move(result);
  }
  else if(type.id() == ID_vhdl_integer)
  {
    return signedbv_typet{32};
  }
  else if(type.id() == ID_vhdl_array)
  {
    auto &array_type = to_vhdl_array_type(type);
    DATA_INVARIANT(
      array_type.is_constrained(),
      "arrays are constrained after type checking");

    auto element_type = vhdl_lowering(array_type.element_type());
    auto length = numeric_cast_v<std::size_t>(array_type.length());

    if(element_type.id() == ID_bool)
    {
      if(array_type.base_name() == "signed")
        return signedbv_typet{length};
      else
        return unsignedbv_typet{length};
    }
    else
      return array_typet{
        element_type, from_integer(length, signedbv_typet{32})};
  }
  else if(type.id() == ID_vhdl_record)
  {
    struct_typet result;
    for(auto &c : to_vhdl_record_type(type).components())
    {
      result.components().emplace_back(c.get_name(), vhdl_lowering(c.type()));
      result.components().back().set_pretty_name(c.get_pretty_name());
    }
    result.add_source_location() = type.source_location();
    return std::move(result);
  }
  else
    return type; // a CBMC type
}

/// the width of a vector or integer type after lowering
static std::size_t width_of(const typet &vhdl_type)
{
  return to_bitvector_type(vhdl_lowering(vhdl_type)).get_width();
}

/// a signed type wide enough for the values of both operands, for
/// true for a constrained array type with no elements
static bool is_null_array(const typet &type)
{
  return type.id() == ID_vhdl_array &&
         to_vhdl_array_type(type).is_constrained() &&
         to_vhdl_array_type(type).length() == 0;
}

/// numeric comparisons at full precision
static signedbv_typet wide_type(const typet &a, const typet &b)
{
  return signedbv_typet{std::max(width_of(a), width_of(b)) + 1};
}

/// IEEE 1076-2008 8.4: the bit position of an index into a vector,
/// counting from the right-most bit, which is bit 0; the index has been
/// lowered to signedbv(32)
static exprt bit_position(const exprt &index, const vhdl_ranget &range)
{
  signedbv_typet integer_type{32};

  if(index.is_constant())
  {
    auto value = numeric_cast_v<mp_integer>(to_constant_expr(index));
    return from_integer(
      range.direction == vhdl_directiont::DOWNTO ? value - range.right
                                                 : range.right - value,
      integer_type);
  }

  if(range.direction == vhdl_directiont::DOWNTO)
    return minus_exprt{index, from_integer(range.right, integer_type)};
  else
    return minus_exprt{from_integer(range.right, integer_type), index};
}

/// the position of an index into an array, counting from 0 for the
/// element with the lowest index
static exprt array_position(const exprt &index, const vhdl_ranget &range)
{
  signedbv_typet integer_type{32};

  if(index.is_constant())
    return from_integer(
      numeric_cast_v<mp_integer>(to_constant_expr(index)) - range.low(),
      integer_type);

  return minus_exprt{index, from_integer(range.low(), integer_type)};
}

/// IEEE 1076-2008 5.2.2.1: the position number of an enumeration
/// value, as a bit-vector, for the relational operators; the
/// expression has been lowered
static exprt enumeration_position(const exprt &expr)
{
  auto &elements = to_enumeration_type(expr.type()).elements();
  unsignedbv_typet position_type{address_bits(elements.size()) + 1};

  // the last literal has the highest position
  exprt result = from_integer(elements.size() - 1, position_type);

  for(std::size_t i = elements.size() - 1; i > 0; i--)
  {
    constant_exprt literal{elements[i - 1].id(), expr.type()};
    result = if_exprt{
      equal_exprt{expr, literal},
      from_integer(i - 1, position_type),
      std::move(result)};
  }

  return result;
}

/// IEEE 1076-2008 9.2.3: the predefined relational operators on
/// one-dimensional arrays compare lexicographically, from the left.
/// The operands are lowered bit-vectors, most significant (left-most)
/// bit first.
static exprt
lexicographic_relation(irep_idt id, const exprt &lhs, const exprt &rhs)
{
  auto lhs_width = to_bitvector_type(lhs.type()).get_width();
  auto rhs_width = to_bitvector_type(rhs.type()).get_width();

  if(lhs_width == rhs_width)
  {
    // the lexicographic order on equal-length bit vectors is the
    // unsigned order
    unsignedbv_typet type{lhs_width};
    return binary_relation_exprt{
      typecast_exprt{lhs, type}, id, typecast_exprt{rhs, type}};
  }

  // Compare the common prefix; if equal, the shorter is less.
  auto common = std::min(lhs_width, rhs_width);
  unsignedbv_typet prefix_type{common};

  exprt lhs_prefix =
    common == 0 ? static_cast<exprt>(from_integer(0, prefix_type))
                : static_cast<exprt>(
                    extractbits_exprt{lhs, lhs_width - common, prefix_type});
  exprt rhs_prefix =
    common == 0 ? static_cast<exprt>(from_integer(0, prefix_type))
                : static_cast<exprt>(
                    extractbits_exprt{rhs, rhs_width - common, prefix_type});

  bool lhs_shorter = lhs_width < rhs_width;

  // lhs < rhs: prefix(lhs) < prefix(rhs), or equal prefixes and lhs shorter
  exprt less = or_exprt{
    binary_relation_exprt{lhs_prefix, ID_lt, rhs_prefix},
    and_exprt{
      equal_exprt{lhs_prefix, rhs_prefix},
      lhs_shorter ? static_cast<exprt>(true_exprt{})
                  : static_cast<exprt>(false_exprt{})}};

  // the arrays have different lengths and are thus not equal
  if(id == ID_lt || id == ID_le)
    return less;
  else // ID_gt, ID_ge
    return not_exprt{less};
}

/// VHDL mod follows the sign of the right operand, whereas CBMC's
/// ID_mod follows the left operand, as in C:
/// a mod b = ((a rem b) + b) rem b
/// The sum is computed one bit wider, as (a rem b) + b may overflow;
/// the result is in the range of b and fits the type.
/// CBMC's euclidean_mod_exprt is not used: its result is never
/// negative, which differs from VHDL for a negative right operand
/// (3 mod -5 is -2), and only the SMT2 back-ends convert it.
static exprt signed_mod(exprt lhs, exprt rhs)
{
  auto type = lhs.type();
  signedbv_typet wide_type{to_bitvector_type(type).get_width() + 1};
  exprt wide_rhs = typecast_exprt{rhs, wide_type};
  exprt rem = binary_exprt{std::move(lhs), ID_mod, std::move(rhs), type};
  exprt sum = plus_exprt{typecast_exprt{std::move(rem), wide_type}, wide_rhs};
  exprt result = binary_exprt{std::move(sum), ID_mod, wide_rhs, wide_type};
  return typecast_exprt{std::move(result), type};
}

/// numeric_std RESIZE of a signed vector to a shorter width keeps the
/// sign bit and the rightmost width-1 bits, unlike a truncation.
static exprt signed_resize(exprt value, std::size_t width)
{
  auto old_width = to_bitvector_type(value.type()).get_width();
  PRECONDITION(width < old_width);
  signedbv_typet type{width};
  exprt sign_bit = extractbit_exprt{value, old_width - 1};
  if(width == 1)
    return typecast_exprt{std::move(sign_bit), type};
  exprt low_bits =
    extractbits_exprt{std::move(value), 0, unsignedbv_typet{width - 1}};
  return concatenation_exprt{
    {std::move(sign_bit), std::move(low_bits)}, std::move(type)};
}

/// the bit-vector constant for a lowered concatenation of constant
/// bits, most significant first
static std::optional<constant_exprt>
constant_bits(const exprt::operandst &bits, const typet &type)
{
  mp_integer value = 0;
  for(auto &bit : bits)
  {
    if(bit.is_true())
      value = value * 2 + 1;
    else if(bit.is_false())
      value = value * 2;
    else
      return {};
  }

  // the signed case: the top bit is the sign
  if(type.id() == ID_signedbv && !bits.empty() && bits.front().is_true())
    value -= power(2, bits.size());

  return from_integer(value, type);
}

/// IEEE 1076-2008 9.2.9: the condition operator ?? on a literal of
/// std_ulogic; 'H' and 'L' are read as '1' and '0'
static std::optional<exprt> lower_condition_literal(const exprt &expr)
{
  if(expr.id() != ID_typecast)
    return {};

  auto &op = to_typecast_expr(expr).op();
  if(
    !op.is_constant() || !is_vhdl_scalar_bit_type(op.type()) ||
    to_vhdl_enumeration_type(expr.type()).base_name() != "boolean")
    return {};

  auto literal = to_constant_expr(op).get_value();
  auto type = vhdl_lowering(expr.type());

  if(literal == "'1'" || literal == "'H'")
    return constant_exprt{ID_true, type};
  else if(literal == "'0'" || literal == "'L'")
    return constant_exprt{ID_false, type};
  else
    return {};
}

exprt vhdl_lowering(exprt expr)
{
  if(expr.id() == ID_typecast && expr.type().id() == ID_vhdl_enumeration)
  {
    auto condition_literal = lower_condition_literal(expr);
    if(condition_literal.has_value())
      return std::move(*condition_literal);
  }

  // The VHDL types of the expression and of the operands are needed
  // after lowering the operands. This is a shallow copy.
  const exprt vhdl_expr = expr;
  const typet &vhdl_type = vhdl_expr.type();
  auto vhdl_operand_type = [&vhdl_expr](std::size_t i) -> const typet &
  { return vhdl_expr.operands()[i].type(); };

  for(auto &op : expr.operands())
    op = vhdl_lowering(op);

  auto id = expr.id();
  auto &source_location = vhdl_expr.source_location();

  // IEEE 1076-2008 5.3.2.2: a null array has no elements; it has no
  // bit-vector counterpart
  if(is_null_array(vhdl_type))
    throw ebmc_errort{}.with_location(source_location)
      << "null arrays are not supported";

  auto lowered_type = vhdl_lowering(vhdl_type);
  expr.type() = lowered_type;

  if(id == ID_constant)
  {
    if(vhdl_type.id() == ID_vhdl_enumeration)
    {
      auto literal = to_constant_expr(expr).get_value();

      if(lowered_type.id() == ID_bool)
      {
        // The design is two-valued: '0' and '1' (and false, true). 'H'
        // and 'L' are distinct values of std_ulogic, and are only
        // supported where they are read as '1' and '0', by the
        // condition operator (see lower_condition_literal).
        if(literal == "true" || literal == "'1'")
          return constant_exprt{ID_true, lowered_type};
        else if(literal == "false" || literal == "'0'")
          return constant_exprt{ID_false, lowered_type};
        else
          throw ebmc_errort{}.with_location(source_location)
            << "the value " << literal << " of "
            << to_vhdl_enumeration_type(vhdl_type).name()
            << " is not supported";
      }

      return expr; // an enumeration constant
    }
    else if(vhdl_type.id() == ID_vhdl_integer)
      return from_integer(
        vhdl_integer_value(to_constant_expr(vhdl_expr)), lowered_type);
    else
      return expr;
  }
  else if(id == ID_array)
  {
    // an array value, with the elements from the left
    if(lowered_type.id() == ID_unsignedbv || lowered_type.id() == ID_signedbv)
    {
      // the left-most element is the most significant bit
      auto constant = constant_bits(expr.operands(), lowered_type);
      if(constant.has_value())
        return std::move(*constant);
      else if(expr.operands().size() == 1)
        return typecast_exprt{expr.operands().front(), lowered_type};
      else
        return concatenation_exprt{std::move(expr.operands()), lowered_type};
    }
    else
    {
      // the elements are stored from the lowest index
      auto &array_type = to_array_type(lowered_type);
      auto operands = std::move(expr.operands());
      if(
        to_vhdl_array_type(vhdl_type).range().direction ==
        vhdl_directiont::DOWNTO)
        std::reverse(operands.begin(), operands.end());
      return array_exprt{std::move(operands), array_type};
    }
  }
  else if(id == ID_array_of)
  {
    auto &element = to_unary_expr(expr).op();
    if(lowered_type.id() == ID_unsignedbv || lowered_type.id() == ID_signedbv)
    {
      auto width = to_bitvector_type(lowered_type).get_width();
      exprt::operandst bits(width, element);
      auto constant = constant_bits(bits, lowered_type);
      if(constant.has_value())
        return std::move(*constant);
      else
        return concatenation_exprt{std::move(bits), lowered_type};
    }
    else
      return array_of_exprt{element, to_array_type(lowered_type)};
  }
  else if(id == ID_struct)
  {
    return struct_exprt{std::move(expr.operands()), lowered_type};
  }
  else if(id == ID_index && vhdl_operand_type(0).id() == ID_vhdl_array)
  {
    auto &array = to_binary_expr(expr).op0();
    auto &index = to_binary_expr(expr).op1();
    auto range = to_vhdl_array_type(vhdl_operand_type(0)).range();

    if(lowers_to_bitvector(vhdl_operand_type(0)))
      return extractbit_exprt{array, bit_position(index, range)};
    else
      return index_exprt{array, array_position(index, range), lowered_type};
  }
  else if(id == ID_vhdl_slice)
  {
    auto &slice = to_vhdl_slice_expr(vhdl_expr);
    auto &prefix = to_binary_expr(expr).op0();
    auto prefix_range = to_vhdl_array_type(slice.prefix().type()).range();
    auto slice_range = to_vhdl_array_type(vhdl_type).range();

    // the lowest bit of the slice
    mp_integer lowest_bit = slice_range.direction == vhdl_directiont::DOWNTO
                              ? slice_range.low() - prefix_range.right
                              : prefix_range.right - slice_range.high();

    if(slice_range.length() == 0)
      return from_integer(0, lowered_type);

    return extractbits_exprt{
      prefix, numeric_cast_v<std::size_t>(lowest_bit), lowered_type};
  }
  else if(id == ID_member && vhdl_operand_type(0).id() == ID_vhdl_record)
  {
    return member_exprt{
      to_unary_expr(expr).op(),
      to_vhdl_member_expr(vhdl_expr).get_component_name(),
      lowered_type};
  }
  else if(id == ID_with && vhdl_operand_type(0).id() == ID_vhdl_array)
  {
    // an array with one element replaced, from the synthesis
    auto &with = to_with_expr(expr);
    auto range = to_vhdl_array_type(vhdl_operand_type(0)).range();

    if(lowers_to_bitvector(vhdl_operand_type(0)))
      return update_bit_exprt{
        with.old(), bit_position(with.where(), range), with.new_value()};
    else
      return with_exprt{
        with.old(), array_position(with.where(), range), with.new_value()};
  }
  else if(id == ID_typecast)
  {
    // type conversions, to_integer, to_unsigned, ??, and the
    // conversions inserted by the type checker; the CBMC typecast
    // truncates or extends according to the signedness
    auto &op = to_typecast_expr(expr).op();
    if(op.type() == lowered_type)
      return op;
    else
      return typecast_exprt{op, lowered_type};
  }
  else if(
    (id == ID_and || id == ID_or || id == ID_nand || id == ID_nor ||
     id == ID_xor || id == ID_xnor) &&
    expr.operands().size() == 2 && vhdl_type.id() == ID_vhdl_array)
  {
    // the logical operators on vectors
    auto &lhs = to_binary_expr(expr).op0();
    auto &rhs = to_binary_expr(expr).op1();
    exprt result;
    if(id == ID_and)
      result = bitand_exprt{lhs, rhs};
    else if(id == ID_or)
      result = bitor_exprt{lhs, rhs};
    else if(id == ID_nand)
      result = bitnot_exprt{bitand_exprt{lhs, rhs}};
    else if(id == ID_nor)
      result = bitnot_exprt{bitor_exprt{lhs, rhs}};
    else if(id == ID_xor)
      result = bitxor_exprt{lhs, rhs};
    else
      result = bitnot_exprt{bitxor_exprt{lhs, rhs}};
    result.type() = lowered_type;
    return result;
  }
  else if(
    (id == ID_and || id == ID_or || id == ID_nand || id == ID_nor ||
     id == ID_xor || id == ID_xnor) &&
    expr.operands().size() == 2 && vhdl_type.id() == ID_vhdl_enumeration)
  {
    // the logical operators on bit, boolean and std_(u)logic
    auto &lhs = to_binary_expr(expr).op0();
    auto &rhs = to_binary_expr(expr).op1();
    if(id == ID_and)
      return and_exprt{lhs, rhs};
    else if(id == ID_or)
      return or_exprt{lhs, rhs};
    else if(id == ID_nand)
      return not_exprt{and_exprt{lhs, rhs}};
    else if(id == ID_nor)
      return not_exprt{or_exprt{lhs, rhs}};
    else if(id == ID_xor)
      return xor_exprt{lhs, rhs};
    else
      return not_exprt{xor_exprt{lhs, rhs}};
  }
  else if(id == ID_not && vhdl_type.id() == ID_vhdl_array)
  {
    return bitnot_exprt{to_unary_expr(expr).op()};
  }
  else if(id == ID_not && vhdl_type.id() == ID_vhdl_enumeration)
  {
    return not_exprt{to_unary_expr(expr).op()};
  }
  else if(
    (id == ID_equal || id == ID_notequal || id == ID_lt || id == ID_le ||
     id == ID_gt || id == ID_ge) &&
    expr.operands().size() == 2 &&
    (vhdl_operand_type(0).id() == ID_vhdl_array ||
     vhdl_operand_type(1).id() == ID_vhdl_array ||
     vhdl_operand_type(0).id() == ID_vhdl_enumeration ||
     vhdl_operand_type(0).id() == ID_vhdl_integer))
  {
    auto &lhs = to_binary_expr(expr).op0();
    auto &rhs = to_binary_expr(expr).op1();
    auto &lhs_type = vhdl_operand_type(0);
    auto &rhs_type = vhdl_operand_type(1);
    bool equality = id == ID_equal || id == ID_notequal;

    if(lhs_type.id() == ID_vhdl_array || rhs_type.id() == ID_vhdl_array)
    {
      bool numeric = is_vhdl_numeric_vector_type(lhs_type) ||
                     is_vhdl_numeric_vector_type(rhs_type);

      if(numeric)
      {
        // numeric_std: at full precision, also with an integer
        auto type = wide_type(lhs_type, rhs_type);
        return binary_relation_exprt{
          typecast_exprt{lhs, type}, id, typecast_exprt{rhs, type}};
      }

      // IEEE 1076-2008 9.2.3: the predefined operators on arrays of
      // the same type, possibly of different lengths
      auto lhs_length = to_vhdl_array_type(lhs_type).length();
      auto rhs_length = to_vhdl_array_type(rhs_type).length();

      if(equality)
      {
        if(lhs_length != rhs_length)
          return id == ID_equal ? static_cast<exprt>(false_exprt{})
                                : static_cast<exprt>(true_exprt{});
        return id == ID_equal ? static_cast<exprt>(equal_exprt{lhs, rhs})
                              : static_cast<exprt>(notequal_exprt{lhs, rhs});
      }
      else
        return lexicographic_relation(id, lhs, rhs);
    }
    else if(equality)
    {
      return id == ID_equal ? static_cast<exprt>(equal_exprt{lhs, rhs})
                            : static_cast<exprt>(notequal_exprt{lhs, rhs});
    }
    else if(lhs_type.id() == ID_vhdl_integer)
    {
      return binary_relation_exprt{lhs, id, rhs};
    }
    else if(lhs.type().id() == ID_bool)
    {
      // false < true, '0' < '1'
      if(id == ID_lt)
        return and_exprt{not_exprt{lhs}, rhs};
      else if(id == ID_le)
        return or_exprt{not_exprt{lhs}, rhs};
      else if(id == ID_gt)
        return and_exprt{lhs, not_exprt{rhs}};
      else
        return or_exprt{lhs, not_exprt{rhs}};
    }
    else
    {
      // IEEE 1076-2008 5.2.2.1: the order of the literals
      return binary_relation_exprt{
        enumeration_position(lhs), id, enumeration_position(rhs)};
    }
  }
  else if(
    (id == ID_plus || id == ID_minus || id == ID_mult || id == ID_div ||
     id == ID_mod || id == ID_vhdl_rem) &&
    expr.operands().size() == 2 &&
    (vhdl_type.id() == ID_vhdl_integer || vhdl_type.id() == ID_vhdl_array))
  {
    // For +, - and *, the operands are extended to the result type:
    // numeric_std multiplication yields the sum of the lengths. For /,
    // rem and mod, the result may be shorter than an operand, so the
    // operation is done at the width of the wider operand, and the
    // result is then resized, as numeric_std does with RESIZE: for
    // signed, this keeps the sign bit and the low bits.
    auto &lhs_op = to_binary_expr(expr).op0();
    auto &rhs_op = to_binary_expr(expr).op1();

    typet compute_type = lowered_type;
    if(id == ID_div || id == ID_mod || id == ID_vhdl_rem)
    {
      auto width = std::max(
        {to_bitvector_type(lowered_type).get_width(),
         to_bitvector_type(lhs_op.type()).get_width(),
         to_bitvector_type(rhs_op.type()).get_width()});
      compute_type = lowered_type.id() == ID_signedbv
                       ? static_cast<typet>(signedbv_typet{width})
                       : static_cast<typet>(unsignedbv_typet{width});
    }

    auto lhs = typecast_exprt::conditional_cast(lhs_op, compute_type);
    auto rhs = typecast_exprt::conditional_cast(rhs_op, compute_type);

    exprt result;
    if(id == ID_mod && compute_type.id() == ID_signedbv)
      result = signed_mod(std::move(lhs), std::move(rhs));
    else
    {
      irep_idt cbmc_id = id == ID_vhdl_rem ? ID_mod : id;
      result =
        binary_exprt{std::move(lhs), cbmc_id, std::move(rhs), compute_type};
    }

    if(
      compute_type.id() == ID_signedbv &&
      to_bitvector_type(lowered_type).get_width() <
        to_bitvector_type(compute_type).get_width())
      return signed_resize(
        std::move(result), to_bitvector_type(lowered_type).get_width());
    else
      return typecast_exprt::conditional_cast(std::move(result), lowered_type);
  }
  else if(
    (id == ID_shl || id == ID_lshr || id == ID_ashr || id == ID_rol ||
     id == ID_ror) &&
    vhdl_type.id() == ID_vhdl_array)
  {
    return shift_exprt{
      to_binary_expr(expr).op0(), id, to_binary_expr(expr).op1()};
  }
  else if(id == ID_concatenation && vhdl_type.id() == ID_vhdl_array)
  {
    if(lowered_type.id() == ID_unsignedbv || lowered_type.id() == ID_signedbv)
    {
      auto constant = constant_bits(expr.operands(), lowered_type);
      if(constant.has_value())
        return std::move(*constant);
      return concatenation_exprt{std::move(expr.operands()), lowered_type};
    }
    else
      throw ebmc_errort{}.with_location(source_location)
        << "concatenation is only supported for vectors";
  }
  else if(
    id == ID_vhdl_event || id == ID_vhdl_rising_edge ||
    id == ID_vhdl_falling_edge)
  {
    throw ebmc_errort{}.with_location(source_location)
      << "clock edge outside of a clock edge condition";
  }
  else
  {
    // other expressions, including those from the synthesis, keep their
    // operator; the types have been lowered
    return expr;
  }
}

void vhdl_lowering(symbol_table_baset &symbol_table)
{
  // the symbols of the VHDL front-end, including the properties
  std::vector<irep_idt> vhdl_symbols;
  for(auto &entry : symbol_table)
    if(
      entry.second.mode == ID_VHDL ||
      id2string(entry.second.module).compare(0, 6, "vhdl::") == 0)
      vhdl_symbols.push_back(entry.first);

  const namespacet ns{symbol_table};

  for(auto &name : vhdl_symbols)
  {
    auto &writeable = symbol_table.get_writeable_ref(name);

    if(writeable.type.id() == ID_module)
    {
      // the ports carry types
      for(auto &port : to_module_type(writeable.type).ports())
        port.type() = vhdl_lowering(port.type());
    }
    else
    {
      if(is_null_array(writeable.type))
        throw ebmc_errort{}.with_location(writeable.location)
          << "null arrays are not supported";
      writeable.type = vhdl_lowering(writeable.type);
    }

    // the simplifier needs CBMC types, so this is the first opportunity
    if(writeable.value.is_not_nil())
      writeable.value = simplify_expr(vhdl_lowering(writeable.value), ns);
  }
}
