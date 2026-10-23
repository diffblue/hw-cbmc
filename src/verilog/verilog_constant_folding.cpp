/*******************************************************************\

Module: Verilog Constant Folding

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_constant_folding.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/expr.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include "aval_bval_encoding.h"
#include "verilog_lowering.h"
#include "verilog_simplifier.h"

/// Lift a lowered constant back to the given four-valued Verilog type.
/// The lowered constant is usually an aval/bval pair of twice the width,
/// but the simplifier may have produced a two-valued constant (a
/// bit-vector of the same width, or a Boolean), and may have dropped the
/// aval/bval type attribute. Hence, decode by width.
static constant_exprt lift_four_valued(
  const constant_exprt &lowered,
  const typet &four_valued_type,
  const source_locationt &source_location)
{
  PRECONDITION(is_four_valued(four_valued_type));

  auto width = to_bitvector_type(four_valued_type).get_width();
  const auto aval_bval_type = lower_to_aval_bval(four_valued_type);

  // the aval/bval encoding of the value
  irep_idt aval_bval_value;

  if(lowered.type().id() == ID_bool)
  {
    DATA_INVARIANT(width == 1, "Boolean constant must have width 1");
    aval_bval_value =
      integer2bvrep(lowered.is_true() ? 1 : 0, aval_bval_type.get_width());
  }
  else
  {
    auto lowered_width = to_bitvector_type(lowered.type()).get_width();
    if(lowered_width == 2 * width)
    {
      aval_bval_value = lowered.get_value();
    }
    else
    {
      DATA_INVARIANT(
        lowered_width == width, "lowered constant must have same width");
      // bval is zero
      aval_bval_value = integer2bvrep(
        bvrep2integer(lowered.get_value(), width, false),
        aval_bval_type.get_width());
    }
  }

  auto result = raise_from_aval_bval(
    constant_exprt{aval_bval_value, aval_bval_type}, four_valued_type);

  // The lowering may have created new expressions without
  // source location; use the one of the original expression.
  result.add_source_location() = source_location;

  return result;
}

exprt verilog_constant_folding(exprt expr, const namespacet &ns)
{
  // This performs constant-folding on a type-checked expression
  // according to Section 11.2.1 IEEE 1800-2017.
  auto verilog_type = expr.type();
  auto source_location = expr.source_location();

  auto expr_lowered = verilog_lowering(std::move(expr));

  // simplify
  auto expr_simplified = verilog_simplifier(std::move(expr_lowered), ns);

  // Lift four-valued constants back to their Verilog type.
  if(
    expr_simplified.is_constant() && is_four_valued(verilog_type) &&
    (expr_simplified.type().id() == ID_bool ||
     can_cast_type<bitvector_typet>(expr_simplified.type())))
  {
    return lift_four_valued(
      to_constant_expr(expr_simplified), verilog_type, source_location);
  }

  return expr_simplified;
}
