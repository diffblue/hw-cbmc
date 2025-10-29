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
  PRECONDITION(is_four_valued(src));
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
  PRECONDITION(is_four_valued(src.type()));

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
  PRECONDITION(dest.id() == ID_bv);
  return concatenation_exprt{{bval, aval}, dest};
}

exprt aval_bval_conversion(const exprt &src, const typet &dest)
{
  PRECONDITION(is_aval_bval(dest));
  auto dest_width = aval_bval_width(dest);

  if(is_aval_bval(src.type()))
  {
    // four-valued to four-valued
    auto src_width = aval_bval_width(src.type());

    if(src_width == dest_width)
    {
      // same size
      return typecast_exprt{src, dest};
    }
    else if(src_width > dest_width)
    {
      // shrink
      auto new_aval = adjust_size(aval(src), dest_width);
      auto new_bval = adjust_size(bval(src), dest_width);
      return combine_aval_bval(new_aval, new_bval, dest);
    }
    else
    {
      // extend
      auto underlying_src = aval_bval_underlying(src.type());
      auto underlying_dest = aval_bval_underlying(dest);

      if(underlying_src.id() == ID_signedbv)
      {
        // sign extend both aval and bval
        auto new_aval = typecast_exprt{
          typecast_exprt{
            typecast_exprt{aval(src), underlying_src}, underlying_dest},
          bv_typet{dest_width}};
        auto new_bval = typecast_exprt{
          typecast_exprt{
            typecast_exprt{bval(src), underlying_src}, underlying_dest},
          bv_typet{dest_width}};
        return combine_aval_bval(new_aval, new_bval, dest);
      }
      else
      {
        auto new_aval = adjust_size(aval(src), dest_width);
        auto new_bval = adjust_size(bval(src), dest_width);
        return combine_aval_bval(new_aval, new_bval, dest);
      }
    }
  }
  else
  {
    // two-valued to four-valued
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

/// return 'x'
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

exprt aval_bval_reduction(const unary_exprt &expr)
{
  auto &type = expr.type();
  auto type_aval_bval = lower_to_aval_bval(type);
  PRECONDITION(is_four_valued(type));
  PRECONDITION(is_aval_bval(expr.op()));

  auto has_xz = ::has_xz(expr.op());
  auto x = make_x(type);
  auto op_aval = aval(expr.op());
  auto op_bval = bval(expr.op());

  if(expr.id() == ID_reduction_xor || expr.id() == ID_reduction_xnor)
  {
    auto reduction_expr = unary_exprt{expr.id(), op_aval, bool_typet{}};
    return if_exprt{has_xz, x, aval_bval_conversion(reduction_expr, x.type())};
  }
  else if(expr.id() == ID_reduction_and || expr.id() == ID_reduction_nand)
  {
    auto has_zero = notequal_exprt{
      bitor_exprt{op_aval, op_bval},
      to_bv_type(op_aval.type()).all_ones_expr()};

    auto one = combine_aval_bval(
      bv_typet{1}.all_ones_expr(),
      bv_typet{1}.all_zeros_expr(),
      type_aval_bval);
    auto zero = combine_aval_bval(
      bv_typet{1}.all_zeros_expr(),
      bv_typet{1}.all_zeros_expr(),
      type_aval_bval);

    if(expr.id() == ID_reduction_and)
    {
      return if_exprt{has_zero, zero, if_exprt{has_xz, x, one}};
    }
    else // nand
    {
      return if_exprt{has_zero, one, if_exprt{has_xz, x, zero}};
    }
  }
  else if(expr.id() == ID_reduction_or || expr.id() == ID_reduction_nor)
  {
    auto has_one = notequal_exprt{
      bitand_exprt{op_aval, bitnot_exprt{op_bval}},
      to_bv_type(op_aval.type()).all_zeros_expr()};

    auto one = combine_aval_bval(
      bv_typet{1}.all_ones_expr(),
      bv_typet{1}.all_zeros_expr(),
      type_aval_bval);
    auto zero = combine_aval_bval(
      bv_typet{1}.all_zeros_expr(),
      bv_typet{1}.all_zeros_expr(),
      type_aval_bval);

    if(expr.id() == ID_reduction_or)
    {
      return if_exprt{has_one, one, if_exprt{has_xz, x, zero}};
    }
    else // nor
    {
      return if_exprt{has_one, zero, if_exprt{has_xz, x, one}};
    }
  }
  else
    PRECONDITION(false);
}

exprt aval_bval(const bitnot_exprt &expr)
{
  auto &type = expr.type();
  PRECONDITION(is_four_valued(type));
  PRECONDITION(is_aval_bval(expr.op()));

  // x/z is done bit-wise.
  // ~z is x.
  auto op_aval = aval(expr.op());
  auto op_bval = bval(expr.op());

  exprt aval = bitor_exprt{
    bitand_exprt{bitnot_exprt{op_bval}, op_bval},                // x/z case
    bitand_exprt{bitnot_exprt{op_aval}, bitnot_exprt{op_bval}}}; // 0/1 case

  return combine_aval_bval(aval, op_bval, lower_to_aval_bval(expr.type()));
}

exprt aval_bval_bitwise(const multi_ary_exprt &expr)
{
  auto &type = expr.type();
  PRECONDITION(is_four_valued(type));
  PRECONDITION(!expr.operands().empty());

  for(auto &op : expr.operands())
    PRECONDITION(is_aval_bval(op));

  // x/z is done bit-wise.
  // Any bit involving x/z is x.

  // bval
  exprt::operandst bval_disjuncts;

  for(auto &op : expr.operands())
    bval_disjuncts.push_back(bval(op));

  auto bval = bitor_exprt{bval_disjuncts, bval_disjuncts.front().type()};

  // aval
  exprt::operandst aval_conjuncts;

  for(auto &op : expr.operands())
    aval_conjuncts.push_back(aval(op));

  exprt aval = bitand_exprt{
    multi_ary_exprt{expr.id(), aval_conjuncts, aval_conjuncts.front().type()},
    bitnot_exprt{bval}}; // 0/1 case

  return combine_aval_bval(aval, bval, lower_to_aval_bval(expr.type()));
}

exprt aval_bval_replication(const replication_exprt &expr)
{
  auto &type = expr.type();
  PRECONDITION(is_four_valued(type));
  PRECONDITION(!is_four_valued(expr.times()));

  auto times_int = numeric_cast_v<mp_integer>(expr.times());

  // separately replicate aval and bval
  auto op_aval = aval(expr.op());
  auto op_bval = bval(expr.op());

  auto replication_type = bv_typet{numeric_cast_v<std::size_t>(
    to_bitvector_type(op_aval.type()).width() * times_int)};

  auto aval_replicated =
    replication_exprt{expr.times(), op_aval, replication_type};
  auto bval_replicated =
    replication_exprt{expr.times(), op_bval, replication_type};

  return combine_aval_bval(
    aval_replicated, bval_replicated, lower_to_aval_bval(type));
}

exprt aval_bval(const power_exprt &expr)
{
  PRECONDITION(is_four_valued(expr.type()));
  PRECONDITION(is_aval_bval(expr.base()));
  PRECONDITION(is_aval_bval(expr.exponent()));

  auto has_xz = or_exprt{::has_xz(expr.base()), ::has_xz(expr.exponent())};
  auto power_expr =
    power_exprt{aval_underlying(expr.base()), aval_underlying(expr.exponent())};
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

/// ->, not SVA implies
exprt aval_bval(const verilog_implies_exprt &expr)
{
  PRECONDITION(is_four_valued(expr.type()));
  PRECONDITION(is_aval_bval(expr.lhs()) || is_aval_bval(expr.rhs()));

  auto has_xz = or_exprt{::has_xz(expr.lhs()), ::has_xz(expr.rhs())};
  auto lhs_boolean =
    typecast_exprt::conditional_cast(aval_underlying(expr.lhs()), bool_typet{});
  auto rhs_boolean =
    typecast_exprt::conditional_cast(aval_underlying(expr.rhs()), bool_typet{});
  auto implies_expr = implies_exprt{lhs_boolean, rhs_boolean};
  auto x = make_x(expr.type());
  return if_exprt{has_xz, x, aval_bval_conversion(implies_expr, x.type())};
}

exprt aval_bval(const typecast_exprt &expr)
{
  auto &dest_type = expr.type();

  PRECONDITION(is_aval_bval(expr.op()));

  if(dest_type.id() == ID_bool)
  {
    // 'true' is defined as a "nonzero known value" (1800-2017 12.4).
    auto op_has_xz = ::has_xz(expr.op());
    auto op_aval = aval(expr.op());
    auto op_aval_zero = to_bv_type(op_aval.type()).all_zeros_expr();
    return and_exprt{
      not_exprt{op_has_xz}, notequal_exprt{op_aval, op_aval_zero}};
  }
  else if(
    dest_type.id() == ID_verilog_unsignedbv ||
    dest_type.id() == ID_verilog_signedbv)
  {
    // four-valued to four-valued
    auto aval_bval_type = lower_to_aval_bval(dest_type);
    return aval_bval_conversion(expr.op(), aval_bval_type);
  }
  else if(dest_type.id() == ID_unsignedbv || dest_type.id() == ID_signedbv)
  {
    // four-valued to two-valued
    return typecast_exprt{aval(expr.op()), dest_type};
  }
  else
    PRECONDITION(false);
}

exprt aval_bval(const shift_exprt &expr)
{
  PRECONDITION(is_four_valued(expr.type()));

  auto distance_has_xz = has_xz(expr.distance());
  auto distance_aval = aval(expr.distance());

  // the shift distance must have a numerical interpretation
  auto distance_aval_casted = typecast_exprt{
    distance_aval,
    unsignedbv_typet{to_bitvector_type(distance_aval.type()).get_width()}};

  // shift aval and bval separately
  auto op_aval = aval(expr.op());
  auto op_bval = bval(expr.op());

  auto aval_shifted = shift_exprt{op_aval, expr.id(), distance_aval_casted};
  auto bval_shifted = shift_exprt{op_bval, expr.id(), distance_aval_casted};

  auto combined = combine_aval_bval(
    aval_shifted, bval_shifted, lower_to_aval_bval(expr.type()));

  auto x = make_x(expr.type());
  return if_exprt{distance_has_xz, x, combined};
}

exprt default_aval_bval_lowering(const exprt &expr)
{
  auto &type = expr.type();

  PRECONDITION(is_four_valued(type));

  exprt::operandst disjuncts;
  for(auto &op : expr.operands())
    disjuncts.push_back(has_xz(op));

  auto has_xz = disjunction(disjuncts);

  exprt two_valued_expr = expr; // copy

  for(auto &op : two_valued_expr.operands())
    op = aval_underlying(op); // replace by aval

  if(type.id() == ID_verilog_unsignedbv)
    two_valued_expr.type() = unsignedbv_typet{to_bitvector_type(type).width()};
  else if(type.id() == ID_verilog_signedbv)
    two_valued_expr.type() = signedbv_typet{to_bitvector_type(type).width()};
  else
    PRECONDITION(false);

  return if_exprt{
    has_xz,
    make_x(type),
    aval_bval_conversion(two_valued_expr, lower_to_aval_bval(type))};
}
