/*******************************************************************\

Module: Verilog Constant Folding

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_constant_folding.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/ieee_float.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <ebmc/ebmc_error.h>

#include "aval_bval_encoding.h"
#include "verilog_expr.h"
#include "verilog_lowering.h"
#include "verilog_simplifier.h"
#include "verilog_types.h"

#include <cmath>
#include <string>

/// Is this one of the integral Verilog constant types, i.e. a type for
/// which a folded constant is represented at the Verilog level?
static bool is_integral_verilog_type(const typet &type)
{
  return type.id() == ID_bool || type.id() == ID_unsignedbv ||
         type.id() == ID_signedbv || type.id() == ID_verilog_unsignedbv ||
         type.id() == ID_verilog_signedbv;
}

static bool is_real_verilog_type(const typet &type)
{
  return type.id() == ID_verilog_real || type.id() == ID_verilog_shortreal ||
         type.id() == ID_verilog_realtime;
}

static bool is_signed_verilog_type(const typet &type)
{
  return type.id() == ID_signedbv || type.id() == ID_verilog_signedbv;
}

static std::size_t integral_width(const typet &type)
{
  PRECONDITION(is_integral_verilog_type(type));
  if(type.id() == ID_bool)
    return 1;
  else
    return to_bitvector_type(type).get_width();
}

static ieee_float_spect real_spec(const typet &type)
{
  PRECONDITION(is_real_verilog_type(type));
  if(type.id() == ID_verilog_shortreal)
    return ieee_float_spect::single_precision();
  else
    return ieee_float_spect::double_precision();
}

/// The 0/1/x/z digits, most-significant first, of a lowered integral
/// constant that is an aval/bval pair of the given Verilog width. The
/// aval occupies the lower 'width' bits, the bval the upper 'width'
/// bits. See the table in aval_bval_encoding.h.
static std::string
digits_from_aval_bval(const constant_exprt &constant, std::size_t width)
{
  auto &value = constant.get_value();

  std::string result(width, '0');
  for(std::size_t i = 0; i < width; i++)
  {
    bool a = get_bvrep_bit(value, width * 2, i);
    bool b = get_bvrep_bit(value, width * 2, i + width);
    char digit = !b ? (a ? '1' : '0') : (a ? 'z' : 'x');
    result[width - 1 - i] = digit;
  }
  return result;
}

/// The 0/1/x/z digits, most-significant first, of a lowered integral
/// constant. The constant is either an aval/bval pair (four-valued) or
/// a plain two-valued bit-vector or Boolean.
static std::string
digits_of_lowered(const constant_exprt &constant, std::size_t verilog_width)
{
  auto &type = constant.type();

  if(is_aval_bval(type))
  {
    return digits_from_aval_bval(constant, aval_bval_width(type));
  }
  else if(type.id() == ID_bool)
  {
    return constant.is_true() ? "1" : "0";
  }
  else
  {
    // A plain bit-vector. The simplifier may drop the aval/bval type
    // attribute, leaving a 'bv' of twice the Verilog width that still
    // encodes an aval/bval pair; recognise it by its width.
    auto width = to_bitvector_type(type).get_width();
    if(type.id() == ID_bv && width == verilog_width * 2)
      return digits_from_aval_bval(constant, verilog_width);

    auto &value = constant.get_value();
    std::string result(width, '0');
    for(std::size_t i = 0; i < width; i++)
      result[width - 1 - i] = get_bvrep_bit(value, width, i) ? '1' : '0';
    return result;
  }
}

/// Build a Verilog constant of type 'verilog_type' from the 0/1/x/z
/// digits (most-significant first), resizing as needed. For a two-valued
/// type, x and z become 0.
static constant_exprt
constant_from_digits(std::string digits, const typet &verilog_type)
{
  PRECONDITION(is_integral_verilog_type(verilog_type));
  auto width = integral_width(verilog_type);

  // Resize to the width of the Verilog type, extending with the
  // most-significant digit for signed types and with 0 otherwise
  // (1800-2017 11.8.3), or truncating.
  if(digits.size() < width)
  {
    char fill = (is_signed_verilog_type(verilog_type) && !digits.empty())
                  ? digits[0]
                  : '0';
    digits = std::string(width - digits.size(), fill) + digits;
  }
  else if(digits.size() > width)
    digits = digits.substr(digits.size() - width);

  if(
    verilog_type.id() == ID_verilog_unsignedbv ||
    verilog_type.id() == ID_verilog_signedbv)
  {
    return constant_exprt{digits, verilog_type};
  }
  else
  {
    // Two-valued: x and z become 0 (1800-2017 6.3.1).
    mp_integer value = 0;
    for(auto digit : digits)
      value = value * 2 + (digit == '1' ? 1 : 0);

    if(verilog_type.id() == ID_bool)
      return value == 0 ? constant_exprt{false_exprt{}}
                        : constant_exprt{true_exprt{}};
    else
      return constant_exprt{integer2bvrep(value, width), verilog_type};
  }
}

/// Lift an integral constant from the back-end encoding to a constant
/// of the Verilog type 'verilog_type'.
static constant_exprt
lift_integral(const constant_exprt &lowered, const typet &verilog_type)
{
  PRECONDITION(is_integral_verilog_type(verilog_type));
  auto digits = digits_of_lowered(lowered, integral_width(verilog_type));
  return constant_from_digits(std::move(digits), verilog_type);
}

/// Lift a real constant from the back-end encoding (a floatbv) to a
/// constant of the Verilog real type 'verilog_type'.
static constant_exprt
lift_real(const constant_exprt &lowered, const typet &verilog_type)
{
  PRECONDITION(is_real_verilog_type(verilog_type));

  auto src_spec = ieee_float_spect{to_floatbv_type(lowered.type())};
  ieee_floatt value{src_spec, ieee_floatt::rounding_modet::ROUND_TO_AWAY};
  value.unpack(bvrep2integer(lowered.get_value(), src_spec.width(), false));

  auto dest_spec = real_spec(verilog_type);
  if(value.spec != dest_spec)
    value.change_spec(dest_spec);

  return constant_exprt{
    integer2bvrep(value.pack(), dest_spec.width()), verilog_type};
}

/// Lift the back-end constant 'lowered' to a constant of the Verilog
/// type 'verilog_type'. Returns nothing if the constant is not one of
/// the lifted encodings.
static std::optional<constant_exprt>
lift(const constant_exprt &lowered, const typet &verilog_type)
{
  if(is_integral_verilog_type(verilog_type))
  {
    auto &lowered_type = lowered.type();
    if(
      is_aval_bval(lowered_type) || lowered_type.id() == ID_bool ||
      lowered_type.id() == ID_unsignedbv || lowered_type.id() == ID_signedbv ||
      lowered_type.id() == ID_bv)
    {
      return lift_integral(lowered, verilog_type);
    }
  }
  else if(is_real_verilog_type(verilog_type))
  {
    if(lowered.type().id() == ID_floatbv)
      return lift_real(lowered, verilog_type);
  }

  return {};
}

/// The 0/1/x/z digits, most-significant first, of a Verilog integral
/// constant (not a lowered one). The signedness is returned as well.
static std::pair<std::string, bool>
digits_of_verilog_constant(const constant_exprt &constant)
{
  auto &type = constant.type();
  bool is_signed = is_signed_verilog_type(type);

  if(type.id() == ID_verilog_unsignedbv || type.id() == ID_verilog_signedbv)
  {
    auto width = integral_width(type);
    auto digits = id2string(constant.get_value());
    for(auto &digit : digits)
      if(digit == '?')
        digit = 'z';
    // 1800-2017 5.7.1: extend with the most-significant digit if x/z,
    // and with 0 otherwise.
    if(digits.size() < width)
    {
      char fill = digits.empty()                           ? '0'
                  : (digits[0] == 'x' || digits[0] == 'z') ? digits[0]
                                                           : '0';
      digits = std::string(width - digits.size(), fill) + digits;
    }
    else if(digits.size() > width)
      digits = digits.substr(digits.size() - width);
    return {std::move(digits), is_signed};
  }
  else if(type.id() == ID_bool)
  {
    return {constant.is_true() ? "1" : "0", false};
  }
  else
  {
    auto width = integral_width(type);
    auto &value = constant.get_value();
    std::string digits(width, '0');
    for(std::size_t i = 0; i < width; i++)
      digits[width - 1 - i] = get_bvrep_bit(value, width, i) ? '1' : '0';
    return {std::move(digits), is_signed};
  }
}

/// The two's complement integer value of the digits, which must not
/// contain x/z.
static mp_integer digits_to_integer(const std::string &digits, bool is_signed)
{
  mp_integer result = 0;
  for(auto digit : digits)
    result = result * 2 + (digit == '1' ? 1 : 0);
  if(is_signed && !digits.empty() && digits[0] == '1')
    result -= power(2, digits.size());
  return result;
}

static bool has_xz(const std::string &digits)
{
  return digits.find_first_of("xz") != std::string::npos;
}

/// The integer value of a constant used as an index/width/bound. Handles
/// the Verilog integral types as well as plain integer/bitvector types
/// (e.g. the integer_typet indices produced by the type checker).
/// Nothing if the constant has an x/z digit.
static std::optional<mp_integer> index_value(const constant_exprt &constant)
{
  auto &type = constant.type();
  if(
    type.id() == ID_bool || type.id() == ID_unsignedbv ||
    type.id() == ID_signedbv || type.id() == ID_verilog_unsignedbv ||
    type.id() == ID_verilog_signedbv)
  {
    auto bits = digits_of_verilog_constant(constant);
    if(has_xz(bits.first))
      return {};
    return digits_to_integer(bits.first, bits.second);
  }
  else
    return numeric_cast<mp_integer>(constant);
}

/// The position of the given declared index in the digit string
/// (most-significant first) of a vector, taking the declared range
/// (offset, increasing) into account. Nothing if out of range.
static std::optional<std::size_t>
digit_position(const typet &vector_type, const mp_integer &index)
{
  mp_integer width = integral_width(vector_type);
  mp_integer offset = 0;
  bool increasing = false;

  if(vector_type.id() != ID_bool)
  {
    auto &v = to_verilog_vector_type(vector_type);
    offset = v.offset();
    increasing = v.increasing();
  }

  mp_integer position =
    increasing ? (width - 1) - (index - offset) : index - offset;

  if(position < 0 || position >= width)
    return {};
  else
    return numeric_cast_v<std::size_t>(position);
}

/// The digit of a vector at the given declared index, 'x' if out of
/// range. 'digits' is most-significant first.
static char
digit_at(const std::string &digits, const typet &type, const mp_integer &index)
{
  auto position = digit_position(type, index);
  // position counts from the least-significant digit, i.e. the end.
  return position.has_value() ? digits[digits.size() - 1 - *position] : 'x';
}

/// The digits of 'src' at the declared indices low..high, most
/// significant first. For a decreasing range the most significant digit
/// of the result is the one at the largest declared index, for an
/// increasing range the one at the smallest (1800-2017 7.4.1). Out-of-
/// range positions are x (1800-2017 11.5.1).
static std::string select_digits(
  const std::string &src,
  const typet &src_type,
  const mp_integer &low,
  const mp_integer &high)
{
  PRECONDITION(low <= high);
  bool increasing = src_type.id() != ID_bool &&
                    to_verilog_vector_type(src_type).increasing();
  std::string result;
  for(mp_integer n = 0; n <= high - low; ++n)
  {
    auto i = increasing ? low + n : high - n;
    result += digit_at(src, src_type, i);
  }
  return result;
}

/// Bit-selects, 1800-2017 11.5.1. Folded at the Verilog level, as the
/// selection depends on the declared range of the source, which the
/// lowering consumes. Out of range is x (0 for two-valued result types).
static std::optional<exprt>
fold_bit_select(const verilog_bit_select_exprt &expr)
{
  if(!expr.src().is_constant() || !expr.index().is_constant())
    return {};
  if(!is_integral_verilog_type(expr.src().type()))
    return {};

  auto src = digits_of_verilog_constant(to_constant_expr(expr.src()));
  auto index = index_value(to_constant_expr(expr.index()));

  char digit;
  if(!index.has_value())
    digit = 'x';
  else
    digit = digit_at(src.first, expr.src().type(), *index);

  return constant_from_digits(std::string(1, digit), expr.type());
}

/// Part-selects [msb:lsb], 1800-2017 11.5.1.
static std::optional<exprt>
fold_part_select(const verilog_non_indexed_part_select_exprt &expr)
{
  if(
    !expr.src().is_constant() || !expr.msb().is_constant() ||
    !expr.lsb().is_constant())
    return {};
  if(!is_integral_verilog_type(expr.src().type()))
    return {};

  auto src = digits_of_verilog_constant(to_constant_expr(expr.src()));
  auto msb = index_value(to_constant_expr(expr.msb()));
  auto lsb = index_value(to_constant_expr(expr.lsb()));
  if(!msb.has_value() || !lsb.has_value())
    return {};

  auto low = std::min(*msb, *lsb);
  auto high = std::max(*msb, *lsb);

  if(high - low + 1 != integral_width(expr.type()))
    return {};

  return constant_from_digits(
    select_digits(src.first, expr.src().type(), low, high), expr.type());
}

/// Indexed part-selects [index +: width] and [index -: width],
/// 1800-2017 11.5.1.
static std::optional<exprt> fold_indexed_part_select(
  const verilog_indexed_part_select_plus_or_minus_exprt &expr)
{
  if(
    !expr.src().is_constant() || !expr.index().is_constant() ||
    !expr.width().is_constant())
    return {};
  if(!is_integral_verilog_type(expr.src().type()))
    return {};

  auto src = digits_of_verilog_constant(to_constant_expr(expr.src()));
  auto index = index_value(to_constant_expr(expr.index()));
  auto width = index_value(to_constant_expr(expr.width()));
  if(!width.has_value())
    return {};

  auto width_int = *width;
  if(width_int <= 0 || width_int != integral_width(expr.type()))
    return {};

  if(!index.has_value())
  {
    return constant_from_digits(
      std::string(numeric_cast_v<std::size_t>(width_int), 'x'), expr.type());
  }

  auto index_int = *index;

  // +: selects the declared indices index..index+width-1,
  // -: selects index-width+1..index.
  mp_integer low, high;
  if(expr.id() == ID_verilog_indexed_part_select_plus)
  {
    low = index_int;
    high = index_int + width_int - 1;
  }
  else
  {
    low = index_int - width_int + 1;
    high = index_int;
  }

  return constant_from_digits(
    select_digits(src.first, expr.src().type(), low, high), expr.type());
}

/// Fold base ** exponent when the exponent is a known negative integer,
/// following 1800-2017 Table 11-4. This is done at the Verilog level
/// because the CBMC simplifier aborts on a power with a negative
/// exponent. Returns nothing if the case does not apply, leaving the
/// expression to the lowering-based folding.
static std::optional<exprt>
fold_power_negative_exponent(const power_exprt &expr)
{
  auto &type = expr.type();
  if(!is_integral_verilog_type(type))
    return {};
  if(!expr.base().is_constant() || !expr.exponent().is_constant())
    return {};

  auto base = digits_of_verilog_constant(to_constant_expr(expr.base()));
  auto exponent = digits_of_verilog_constant(to_constant_expr(expr.exponent()));

  // An x/z exponent, or a negative-power case with an x/z base, yields x.
  bool exponent_has_xz =
    exponent.first.find_first_of("xz") != std::string::npos;
  if(exponent_has_xz)
    return {};

  auto exponent_value = digits_to_integer(exponent.first, exponent.second);
  if(exponent_value >= 0)
    return {}; // not our case

  bool base_has_xz = base.first.find_first_of("xz") != std::string::npos;

  // Per Table 11-4: base 0 to a negative power is x; base 1 gives 1;
  // base -1 gives 1 or -1 by the parity of the exponent; otherwise 0.
  auto width = integral_width(type);
  std::string result_digits;

  if(base_has_xz)
  {
    result_digits = std::string(width, 'x');
  }
  else
  {
    auto base_value = digits_to_integer(base.first, base.second);
    if(base_value == 0)
    {
      // x, i.e. 0 for a two-valued type.
      result_digits = std::string(width, 'x');
    }
    else
    {
      mp_integer result;
      if(base_value == 1)
        result = 1;
      else if(base_value == -1)
        result = (exponent_value % 2 == 0) ? 1 : -1;
      else
        result = 0;

      // Two's complement, modulo 2^width.
      auto modulus = power(2, width);
      auto reduced = result % modulus;
      if(reduced < 0)
        reduced += modulus;
      result_digits.resize(width, '0');
      for(std::size_t i = 0; i < width; i++)
      {
        result_digits[width - 1 - i] = ((reduced % 2) == 1) ? '1' : '0';
        reduced /= 2;
      }
    }
  }

  return constant_from_digits(std::move(result_digits), type);
}

/// Fold an arithmetic operator on real operands. The CBMC simplifier
/// does not reliably fold floating-point operations (in particular
/// division and power), so this is done here with ieee_floatt. Returns
/// nothing if the operands are not real constants or the operator is
/// not supported.
static std::optional<exprt> fold_real(const exprt &expr)
{
  if(!is_real_verilog_type(expr.type()))
    return {};

  for(auto &op : expr.operands())
    if(!op.is_constant())
      return {};

  auto read_real = [](const constant_exprt &c) {
    auto spec = real_spec(c.type());
    ieee_floatt f{spec, ieee_floatt::rounding_modet::ROUND_TO_AWAY};
    f.unpack(bvrep2integer(c.get_value(), spec.width(), false));
    return f;
  };

  auto make_result = [&](double value) -> exprt {
    auto spec = real_spec(expr.type());
    ieee_floatt f{spec, ieee_floatt::rounding_modet::ROUND_TO_AWAY};
    f.from_double(value);
    if(f.spec != spec)
      f.change_spec(spec);
    return constant_exprt{integer2bvrep(f.pack(), spec.width()), expr.type()};
  };

  auto id = expr.id();

  if(id == ID_unary_plus)
    return to_unary_expr(expr).op();
  else if(id == ID_unary_minus)
  {
    auto op = read_real(to_constant_expr(to_unary_expr(expr).op()));
    return make_result(-op.to_double());
  }
  else if(id == ID_plus || id == ID_minus || id == ID_mult || id == ID_div)
  {
    auto &binary = to_binary_expr(expr);
    auto lhs = read_real(to_constant_expr(binary.lhs())).to_double();
    auto rhs = read_real(to_constant_expr(binary.rhs())).to_double();
    double result;
    if(id == ID_plus)
      result = lhs + rhs;
    else if(id == ID_minus)
      result = lhs - rhs;
    else if(id == ID_mult)
      result = lhs * rhs;
    else
      result = lhs / rhs; // division by zero yields +/- infinity
    return make_result(result);
  }
  else if(id == ID_power)
  {
    auto &power = to_power_expr(expr);
    auto base = read_real(to_constant_expr(power.base())).to_double();
    auto exponent = read_real(to_constant_expr(power.exponent())).to_double();
    return make_result(std::pow(base, exponent));
  }
  else
    return {};
}

/// The conditional operator, 1800-2017 11.4.11, folded to match the
/// aval/bval encoding: a condition with an x/z digit is ambiguous (even
/// if it has a 1 digit), in which case an integral result is all x and a
/// real result is not folded; otherwise the nonzero/zero condition
/// selects an operand. Returns nothing if the operands are not suitable
/// constants.
static std::optional<exprt> fold_conditional(const if_exprt &expr)
{
  if(!expr.cond().is_constant())
    return {};

  auto &type = expr.type();
  if(!is_integral_verilog_type(type) && !is_real_verilog_type(type))
    return {};

  auto &cond_type = expr.cond().type();
  bool cond_true, cond_ambiguous;

  if(is_integral_verilog_type(cond_type))
  {
    auto cond = digits_of_verilog_constant(to_constant_expr(expr.cond()));
    cond_ambiguous = has_xz(cond.first);
    cond_true = cond.first.find('1') != std::string::npos;
  }
  else
    return {}; // unusual condition type; leave to the lowering

  if(cond_ambiguous)
  {
    if(is_integral_verilog_type(type))
      return constant_from_digits(
        std::string(integral_width(type), 'x'), type);
    else
      return {}; // real result with an ambiguous condition is not folded
  }

  auto &selected = cond_true ? expr.true_case() : expr.false_case();
  if(!selected.is_constant())
    return {};
  return selected;
}

exprt verilog_constant_folding(exprt expr, const namespacet &ns)
{
  // Fold the operands first.
  bool operands_are_constant = true;

  for(auto &op : expr.operands())
  {
    op = verilog_constant_folding(op, ns);
    if(!op.is_constant())
      operands_are_constant = false;
  }

  // The unsized literals are constants.
  if(expr.id() == ID_verilog_unbased_unsized_literal)
  {
    auto location = expr.source_location();
    auto result = to_verilog_unbased_unsized_literal_expr(expr).expand();
    if(location.is_not_nil())
      result.add_source_location() = location;
    return std::move(result);
  }
  else if(expr.id() == ID_verilog_based_unsized_literal)
  {
    auto location = expr.source_location();
    auto result = to_verilog_based_unsized_literal_expr(expr).lower();
    if(location.is_not_nil())
      result.add_source_location() = location;
    return std::move(result);
  }

  if(expr.is_constant() || !operands_are_constant)
    return expr;

  // We only fold expressions whose Verilog type we know how to lift
  // back from the back-end encoding.
  auto &verilog_type = expr.type();
  if(
    !is_integral_verilog_type(verilog_type) &&
    !is_real_verilog_type(verilog_type))
  {
    return expr;
  }

  // A cast from a real constant to Boolean is folded directly: the
  // lowering does not reliably fold it. A real is true iff it is
  // nonzero.
  if(
    expr.id() == ID_typecast && verilog_type.id() == ID_bool &&
    to_typecast_expr(expr).op().is_constant() &&
    is_real_verilog_type(to_typecast_expr(expr).op().type()))
  {
    auto &op = to_constant_expr(to_typecast_expr(expr).op());
    auto spec = real_spec(op.type());
    ieee_floatt f{spec, ieee_floatt::rounding_modet::ROUND_TO_AWAY};
    f.unpack(bvrep2integer(op.get_value(), spec.width(), false));
    auto location = expr.source_location();
    exprt result = f.is_zero() ? static_cast<exprt>(false_exprt{})
                               : static_cast<exprt>(true_exprt{});
    if(location.is_not_nil())
      result.add_source_location() = location;
    return result;
  }

  // Streaming concatenations are left alone: they are not a
  // constant-folding target and their lowering is not meaningful for a
  // bare constant operand.
  if(
    expr.id() == ID_verilog_streaming_concatenation_left_to_right ||
    expr.id() == ID_verilog_streaming_concatenation_right_to_left)
  {
    return expr;
  }

  // Real arithmetic is folded directly with ieee_floatt, as the CBMC
  // simplifier does not reliably fold floating-point operations (in
  // particular division and power), and the lowering has no floatbv
  // power.
  if(is_real_verilog_type(verilog_type))
  {
    auto location = expr.source_location();
    auto folded = fold_real(expr);
    if(folded.has_value())
    {
      if(location.is_not_nil())
        folded->add_source_location() = location;
      return std::move(*folded);
    }
  }

  // A power with a negative exponent is folded directly, as the CBMC
  // simplifier aborts on it.
  if(expr.id() == ID_power && is_integral_verilog_type(verilog_type))
  {
    auto location = expr.source_location();
    auto folded = fold_power_negative_exponent(to_power_expr(expr));
    if(folded.has_value())
    {
      if(location.is_not_nil())
        folded->add_source_location() = location;
      return std::move(*folded);
    }
  }

  // The conditional operator is folded directly to match the aval/bval
  // encoding and to avoid a real-typed if, which the lowering does not
  // handle for a non-Boolean (four-valued) condition. An if that is not
  // folded is left as is rather than lowered.
  if(expr.id() == ID_if)
  {
    auto location = expr.source_location();
    auto folded = fold_conditional(to_if_expr(expr));
    if(folded.has_value())
    {
      if(location.is_not_nil())
        folded->add_source_location() = location;
      return std::move(*folded);
    }
    return expr;
  }

  // Bit-selects and part-selects are folded at the Verilog level: the
  // selection depends on the declared range (offset, increasing) of the
  // source vector, which the lowering consumes while lowering the
  // operands, so these do not round-trip through the lowering.
  {
    auto location = expr.source_location();
    std::optional<exprt> folded;
    if(expr.id() == ID_verilog_bit_select)
      folded = fold_bit_select(to_verilog_bit_select_expr(expr));
    else if(expr.id() == ID_verilog_non_indexed_part_select)
      folded =
        fold_part_select(to_verilog_non_indexed_part_select_expr(expr));
    else if(
      expr.id() == ID_verilog_indexed_part_select_plus ||
      expr.id() == ID_verilog_indexed_part_select_minus)
    {
      folded = fold_indexed_part_select(
        to_verilog_indexed_part_select_plus_or_minus_expr(expr));
    }

    if(folded.has_value())
    {
      if(location.is_not_nil())
        folded->add_source_location() = location;
      return std::move(*folded);
    }

    if(
      expr.id() == ID_verilog_bit_select ||
      expr.id() == ID_verilog_non_indexed_part_select ||
      expr.id() == ID_verilog_indexed_part_select_plus ||
      expr.id() == ID_verilog_indexed_part_select_minus)
    {
      return expr;
    }
  }

  // Fold by lowering the expression to the back-end encoding and
  // running the CBMC simplifier. The verilog_simplifier may throw for
  // constructs it cannot fold (e.g. $countones of a four-valued
  // operand, to which the xor reductions lower); treat that as unfolded.
  exprt simplified;
  try
  {
    auto lowered = verilog_lowering(expr);
    simplified = verilog_simplifier(std::move(lowered), ns);
  }
  catch(const ebmc_errort &)
  {
    return expr;
  }

  // The simplifier may leave a top-level conditional with a constant
  // condition when a sibling branch does not simplify (e.g. the
  // division in the four-valued div/mod lowering, which is unreachable
  // for a zero divisor). Pick the live branch.
  while(simplified.id() == ID_if && to_if_expr(simplified).cond().is_constant())
  {
    auto &if_expr = to_if_expr(simplified);
    auto branch =
      if_expr.cond().is_true() ? if_expr.true_case() : if_expr.false_case();
    simplified = std::move(branch);
  }

  if(!simplified.is_constant())
    return expr;

  // Lift the back-end constant back to the Verilog type.
  auto lifted = lift(to_constant_expr(simplified), verilog_type);

  if(!lifted.has_value())
    return expr;

  // Keep the source location.
  auto location = expr.source_location();
  if(location.is_not_nil())
    lifted->add_source_location() = location;

  return std::move(*lifted);
}
