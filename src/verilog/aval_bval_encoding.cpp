/*******************************************************************\

Module: aval/bval encoding

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "aval_bval_encoding.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>
#include <util/std_expr.h>

#include "verilog_types.h"

bool is_four_valued(const typet &type)
{
  return type.id() == ID_verilog_unsignedbv || type.id() == ID_verilog_signedbv;
}

bool is_four_valued(const exprt &expr)
{
  return is_four_valued(expr.type());
}

bv_typet aval_bval_type(std::size_t width, irep_idt source_type)
{
  PRECONDITION(!source_type.empty());
  auto result = bv_typet{width * 2};
  result.set(ID_C_verilog_aval_bval, source_type);
  return result;
}

bv_typet lower_to_aval_bval(const typet &src)
{
  PRECONDITION(
    src.id() == ID_verilog_unsignedbv || src.id() == ID_verilog_signedbv);
  return aval_bval_type(to_bitvector_type(src).get_width(), src.id());
}

bool is_aval_bval(const typet &type)
{
  return type.id() == ID_bv && !type.get(ID_C_verilog_aval_bval).empty();
}

bool is_aval_bval(const exprt &expr)
{
  return is_aval_bval(expr.type());
}

std::size_t aval_bval_width(const typet &type)
{
  PRECONDITION(is_aval_bval(type));
  return to_bv_type(type).get_width() / 2;
}

std::size_t aval_bval_width(const exprt &expr)
{
  return aval_bval_width(expr.type());
}

typet aval_bval_underlying(const typet &src)
{
  auto id = src.get(ID_C_verilog_aval_bval);
  if(id == ID_verilog_unsignedbv)
    return unsignedbv_typet{aval_bval_width(src)};
  else if(id == ID_verilog_signedbv)
    return signedbv_typet{aval_bval_width(src)};
  else
    PRECONDITION(false);
}

constant_exprt lower_to_aval_bval(const constant_exprt &src)
{
  PRECONDITION(
    src.type().id() == ID_verilog_signedbv ||
    src.type().id() == ID_verilog_unsignedbv);

  auto new_type = lower_to_aval_bval(src.type());
  auto width = aval_bval_width(new_type);
  auto &value = id2string(src.get_value());

  auto bv_f = [width, value](const std::size_t dest_index) {
    bool bval = dest_index >= width;
    std::size_t src_bit_nr = bval ? dest_index - width : dest_index;

    // bval aval | 4-state Verilog value
    // ----------|----------------------
    //   0    0  |   0
    //   0    1  |   1
    //   1    0  |   X
    //   1    1  |   Z

    switch(value[value.size() - 1 - src_bit_nr])
    {
    case '0':
      return bval ? 0 : 0;
    case '1':
      return bval ? 0 : 1;
    case 'x':
      return bval ? 1 : 0;
    case '?':
    case 'z':
      return bval ? 1 : 1;
    default:
      INVARIANT(false, "unexpected Verilog vector bit");
    }
  };

  return constant_exprt{make_bvrep(width * 2, bv_f), new_type};
}

exprt aval(const exprt &src)
{
  if(is_aval_bval(src.type()))
  {
    auto width = aval_bval_width(src.type());
    return extractbits_exprt{src, 0, bv_typet{width}};
  }
  else
  {
    auto width = to_bitvector_type(src.type()).get_width();
    return typecast_exprt::conditional_cast(src, bv_typet{width});
  }
}

exprt aval_underlying(const exprt &src)
{
  if(is_aval_bval(src.type()))
  {
    auto type = aval_bval_underlying(src.type());
    if(type.id() == ID_bool)
      return extractbit_exprt{src, 0};
    else
      return extractbits_exprt{src, 0, type};
  }
  else
  {
    // It's two-valued.
    return src;
  }
}

exprt bval(const exprt &src)
{
  if(is_aval_bval(src.type()))
  {
    auto width = aval_bval_width(src.type());
    return extractbits_exprt{src, width, bv_typet{width}};
  }
  else
  {
    // zeros, signaling 0/1
    auto width = to_bitvector_type(src.type()).get_width();
    return bv_typet{width}.all_zeros_expr();
  }
}

static exprt adjust_size(const exprt &src, std::size_t dest_width)
{
  auto src_width = to_bv_type(src.type()).get_width();
  if(dest_width > src_width)
  {
    auto zeros = bv_typet{dest_width - src_width}.all_zeros_expr();
    return concatenation_exprt{{zeros, src}, bv_typet{dest_width}};
  }
  else if(dest_width < src_width)
  {
    return extractbits_exprt{src, 0, bv_typet{dest_width}};
  }
  else
    return src;
}

static exprt
combine_aval_bval(const exprt &aval, const exprt &bval, const typet &dest)
{
  PRECONDITION(aval.type().id() == ID_bv);
  PRECONDITION(bval.type().id() == ID_bv);
  return concatenation_exprt{{bval, aval}, dest};
}

exprt aval_bval_conversion(const exprt &src, const typet &dest)
{
  PRECONDITION(is_aval_bval(dest));
  auto dest_width = aval_bval_width(dest);

  if(is_aval_bval(src.type()))
  {
    auto src_width = aval_bval_width(src.type());

    if(src_width == dest_width)
    {
      // same size
      return typecast_exprt{src, dest};
    }
    else
    {
      auto new_aval = adjust_size(aval(src), dest_width);
      auto new_bval = adjust_size(bval(src), dest_width);
      return combine_aval_bval(new_aval, new_bval, dest);
    }
  }
  else
  {
    const bv_typet bv_type{dest_width};
    auto aval =
      typecast_exprt{typecast_exprt{src, aval_bval_underlying(dest)}, bv_type};
    auto bval = bv_type.all_zeros_expr();
    return combine_aval_bval(aval, bval, dest);
  }
}

static exprt concatenate(const exprt::operandst &operands)
{
  std::size_t width = 0;
  for(auto &op : operands)
    width += to_bv_type(op.type()).get_width();

  return concatenation_exprt{operands, bv_typet{width}};
}

exprt aval_bval_concatenation(
  const exprt::operandst &operands,
  const typet &type)
{
  exprt::operandst new_aval, new_bval;

  for(auto &op : operands)
  {
    new_aval.push_back(aval(op));
    new_bval.push_back(bval(op));
  }

  return combine_aval_bval(concatenate(new_aval), concatenate(new_bval), type);
}

/// return true iff 'expr' contains either x or z
exprt has_xz(const exprt &expr)
{
  if(is_aval_bval(expr))
  {
    auto width = aval_bval_width(expr);
    return notequal_exprt{bval(expr), bv_typet{width}.all_zeros_expr()};
  }
  else if(is_four_valued(expr))
  {
    // You forgot the encoding.
    PRECONDITION(false);
  }
  else
    return false_exprt{}; // it's two-valued
}

/// return 'x', one bit, in aval_bval encoding
exprt make_x(const typet &type)
{
  PRECONDITION(is_four_valued(type));
  auto width = to_bitvector_type(type).get_width();
  return lower_to_aval_bval(constant_exprt{std::string(width, 'x'), type});
}

exprt aval_bval(const verilog_logical_equality_exprt &expr)
{
  auto &type = expr.type();
  PRECONDITION(type.id() == ID_verilog_unsignedbv);
  // returns 'x' if either operand contains x or z
  auto has_xz = or_exprt{::has_xz(expr.lhs()), ::has_xz(expr.rhs())};
  auto equality = equal_exprt{expr.lhs(), expr.rhs()};
  return if_exprt{
    has_xz,
    make_x(type),
    aval_bval_conversion(equality, lower_to_aval_bval(type))};
}

exprt aval_bval(const verilog_logical_inequality_exprt &expr)
{
  auto &type = expr.type();
  PRECONDITION(type.id() == ID_verilog_unsignedbv);
  // returns 'x' if either operand contains x or z
  auto has_xz = or_exprt{::has_xz(expr.lhs()), ::has_xz(expr.rhs())};
  auto equality = notequal_exprt{expr.lhs(), expr.rhs()};
  return if_exprt{
    has_xz,
    make_x(type),
    aval_bval_conversion(equality, lower_to_aval_bval(type))};
}

exprt aval_bval(const verilog_wildcard_equality_exprt &expr)
{
  auto &type = expr.type();
  PRECONDITION(type.id() == ID_verilog_unsignedbv);

  // We are using masking based on the pattern given as rhs.
  // The aval is the comparison value, and the
  // negation of bval is the mask.
  const auto &pattern_aval = ::aval(expr.rhs());
  const auto &pattern_bval = ::bval(expr.rhs());
  auto mask_expr = bitnot_exprt{pattern_bval};

  return equal_exprt{
    bitand_exprt{aval(expr.lhs()), mask_expr},
    bitand_exprt{pattern_aval, mask_expr}};
}

exprt aval_bval(const verilog_wildcard_inequality_exprt &expr)
{
  auto &type = expr.type();
  PRECONDITION(type.id() == ID_verilog_unsignedbv);

  // We are using masking based on the pattern given as rhs.
  // The aval is the comparison value, and the
  // negation of bval is the mask.
  const auto &pattern_aval = ::aval(expr.rhs());
  const auto &pattern_bval = ::bval(expr.rhs());
  auto mask_expr = bitnot_exprt{pattern_bval};

  return notequal_exprt{
    bitand_exprt{aval(expr.lhs()), mask_expr},
    bitand_exprt{pattern_aval, mask_expr}};
}

exprt aval_bval(const not_exprt &expr)
{
  auto &type = expr.type();
  PRECONDITION(is_four_valued(type));
  PRECONDITION(is_aval_bval(expr.op()));

  auto has_xz = ::has_xz(expr.op());
  auto not_expr =
    not_exprt{extractbit_exprt{expr.op(), natural_typet{}.zero_expr()}};
  auto x = make_x(type);
  return if_exprt{has_xz, x, aval_bval_conversion(not_expr, x.type())};
}

exprt aval_bval(const power_exprt &expr)
{
  PRECONDITION(is_four_valued(expr.type()));
  PRECONDITION(is_aval_bval(expr.lhs()));
  PRECONDITION(is_aval_bval(expr.rhs()));

  auto has_xz = or_exprt{::has_xz(expr.lhs()), ::has_xz(expr.rhs())};
  auto power_expr =
    power_exprt{aval_underlying(expr.lhs()), aval_underlying(expr.rhs())};
  auto x = make_x(expr.type());
  return if_exprt{has_xz, x, aval_bval_conversion(power_expr, x.type())};
}

/// <->, not SVA iff
exprt aval_bval(const verilog_iff_exprt &expr)
{
  PRECONDITION(is_four_valued(expr.type()));
  PRECONDITION(is_aval_bval(expr.lhs()) || is_aval_bval(expr.rhs()));

  auto has_xz = or_exprt{::has_xz(expr.lhs()), ::has_xz(expr.rhs())};
  auto lhs_boolean =
    typecast_exprt::conditional_cast(aval_underlying(expr.lhs()), bool_typet{});
  auto rhs_boolean =
    typecast_exprt::conditional_cast(aval_underlying(expr.rhs()), bool_typet{});
  auto equal_expr = equal_exprt{lhs_boolean, rhs_boolean};
  auto x = make_x(expr.type());
  return if_exprt{has_xz, x, aval_bval_conversion(equal_expr, x.type())};
}

exprt aval_bval(const typecast_exprt &expr)
{
  // 'true' is defined as a "nonzero known value" (1800-2017 12.4).
  PRECONDITION(is_aval_bval(expr.op()));
  PRECONDITION(expr.type().id() == ID_bool);

  auto op_has_xz = ::has_xz(expr.op());
  auto op_aval = aval(expr.op());
  auto op_aval_zero = to_bv_type(op_aval.type()).all_zeros_expr();
  return and_exprt{not_exprt{op_has_xz}, notequal_exprt{op_aval, op_aval_zero}};
}
