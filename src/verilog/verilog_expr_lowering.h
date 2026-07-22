/*******************************************************************\

Module: Verilog Expression Lowering

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Provides lowering of Verilog expressions that have no direct SMV
/// language equivalent, such as reduction operators and replication.

#ifndef CPROVER_VERILOG_VERILOG_EXPR_LOWERING_H
#define CPROVER_VERILOG_VERILOG_EXPR_LOWERING_H

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/std_expr.h>

/// Lower reduction_and to equality with all-ones constant.
/// reduction_and(a) ≡ (a = 0xFF...F)
inline exprt lower(const reduction_and_exprt &expr)
{
  auto &op = expr.op();
  return equal_exprt{op, to_bitvector_type(op.type()).all_ones_expr()};
}

/// Lower reduction_nand to inequality with all-ones constant.
/// reduction_nand(a) ≡ (a != 0xFF...F)
inline exprt lower(const reduction_nand_exprt &expr)
{
  auto &op = expr.op();
  return notequal_exprt{op, to_bitvector_type(op.type()).all_ones_expr()};
}

/// Lower reduction_or to inequality with zero.
/// reduction_or(a) ≡ (a != 0)
inline exprt lower(const reduction_or_exprt &expr)
{
  auto &op = expr.op();
  return notequal_exprt{op, to_bitvector_type(op.type()).all_zeros_expr()};
}

/// Lower reduction_nor to equality with zero.
/// reduction_nor(a) ≡ (a = 0)
inline exprt lower(const reduction_nor_exprt &expr)
{
  auto &op = expr.op();
  return equal_exprt{op, to_bitvector_type(op.type()).all_zeros_expr()};
}

/// Lower reduction_xor to XOR of all individual bits.
/// reduction_xor(a) ≡ a[0] ^ a[1] ^ ... ^ a[n-1]
inline exprt lower(const reduction_xor_exprt &expr)
{
  auto &op = expr.op();
  auto width = to_bitvector_type(op.type()).width();
  exprt result = extractbit_exprt{op, from_integer(0, natural_typet{})};
  for(std::size_t i = 1; i < width; i++)
  {
    result =
      xor_exprt{result, extractbit_exprt{op, from_integer(i, natural_typet{})}};
  }
  return result;
}

/// Lower reduction_xnor to negation of XOR of all individual bits.
/// reduction_xnor(a) ≡ !(a[0] ^ a[1] ^ ... ^ a[n-1])
inline exprt lower(const reduction_xnor_exprt &expr)
{
  auto &op = expr.op();
  auto width = to_bitvector_type(op.type()).width();
  exprt result = extractbit_exprt{op, from_integer(0, natural_typet{})};
  for(std::size_t i = 1; i < width; i++)
  {
    result =
      xor_exprt{result, extractbit_exprt{op, from_integer(i, natural_typet{})}};
  }
  return not_exprt{result};
}

/// Lower replication to concatenation.
/// {N{x}} ≡ x :: x :: ... :: x (N times)
inline exprt lower(const replication_exprt &expr)
{
  auto times = numeric_cast_v<std::size_t>(expr.times());
  exprt::operandst ops;
  ops.reserve(times);
  for(std::size_t i = 0; i < times; i++)
    ops.push_back(expr.op());
  return concatenation_exprt{std::move(ops), expr.type()};
}

#endif // CPROVER_VERILOG_VERILOG_EXPR_LOWERING_H
