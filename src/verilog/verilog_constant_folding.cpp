/*******************************************************************\

Module: Verilog Constant Folding

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_constant_folding.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/expr.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include "aval_bval_encoding.h"
#include "verilog_lowering.h"
#include "verilog_simplifier.h"
#include "verilog_types.h"

/// Lift a lowered constant back to the given four-valued Verilog type.
/// The lowered constant is an aval/bval pair of twice the width when it
/// contains x/z. Otherwise it is two-valued: a bit-vector of the same
/// width, or a Boolean, and the simplifier may have dropped the aval/bval
/// type attribute. Hence, decode by width. In line with the typing of
/// literals, a value without x/z gets the two-valued vector type.
static constant_exprt lift_four_valued(
  const constant_exprt &lowered,
  const typet &four_valued_type,
  const source_locationt &source_location)
{
  PRECONDITION(is_four_valued(four_valued_type));

  auto width = to_bitvector_type(four_valued_type).get_width();
  const auto aval_bval_type = lower_to_aval_bval(four_valued_type);
  const auto two_valued_type = two_valued_vector_type(four_valued_type);

  auto lift = [&]() -> constant_exprt
  {
    if(lowered.type().id() == ID_bool)
    {
      DATA_INVARIANT(width == 1, "Boolean constant must have width 1");
      return from_integer(lowered.is_true() ? 1 : 0, two_valued_type);
    }

    auto lowered_width = to_bitvector_type(lowered.type()).get_width();

    if(lowered_width == 2 * width)
    {
      constant_exprt aval_bval_constant{lowered.get_value(), aval_bval_type};

      if(aval_bval_has_xz(aval_bval_constant))
        return raise_from_aval_bval(aval_bval_constant, four_valued_type);

      // the aval is the lower half
      auto aval =
        bvrep2integer(lowered.get_value(), 2 * width, false) % power(2, width);
      return constant_exprt{integer2bvrep(aval, width), two_valued_type};
    }

    DATA_INVARIANT(
      lowered_width == width, "lowered constant must have same width");
    return constant_exprt{lowered.get_value(), two_valued_type};
  };

  auto result = lift();

  // The lowering may have created new expressions without
  // source location; use the one of the original expression.
  result.add_source_location() = source_location;

  return result;
}

/// Given a lowered expression and the Verilog type of the expression it
/// was lowered from, lift the expression back to the Verilog type if it
/// is a constant. Non-constant expressions are returned as given.
static exprt
verilog_lift_constant(exprt lowered, const typet &verilog_type_given)
{
  // The result is a value, and hence has the range [size-1:0] rather
  // than any declared range of the expression.
  auto verilog_type = verilog_type_given;
  verilog_type.remove(ID_C_offset);
  verilog_type.remove(ID_C_increasing);

  // Only constants are lifted.
  if(!lowered.is_constant())
    return lowered;

  // Lifted already, e.g., an element of an aggregate.
  // The comparison ignores the attributes; hence, set the type.
  if(lowered.type() == verilog_type)
  {
    lowered.type() = verilog_type;
    return lowered;
  }

  // Lift four-valued constants back to their Verilog type, unless they
  // are two-valued.
  if(
    is_four_valued(verilog_type) &&
    (lowered.type().id() == ID_bool ||
     can_cast_type<bitvector_typet>(lowered.type())))
  {
    return lift_four_valued(
      to_constant_expr(lowered), verilog_type, lowered.source_location());
  }
  else if(
    (verilog_type.id() == ID_verilog_real ||
     verilog_type.id() == ID_verilog_shortreal ||
     verilog_type.id() == ID_verilog_realtime) &&
    lowered.type().id() == ID_floatbv)
  {
    // The encoding does not change, only the type does.
    lowered.type() = verilog_type;
  }
  else if(verilog_lowering(verilog_type) == lowered.type())
  {
    // The lowering does not change the type; restore the Verilog type,
    // which may carry attributes (e.g. of an enum) that the simplifier
    // dropped.
    lowered.type() = verilog_type;
  }

  return lowered;
}

/// The lowering lowers the elements of struct, union and array
/// expressions, but not their types. Fold the elements, and lift them
/// back to the element type, to restore type consistency.
static void lift_aggregate_elements(exprt &expr, const namespacet &ns)
{
  for(auto &op : expr.operands())
    lift_aggregate_elements(op, ns);

  auto lift_element = [&ns](exprt &op, const typet &element_type)
  {
    auto source_location = op.source_location();
    auto simplified = verilog_simplifier(op, ns);
    if(simplified.is_constant())
      simplified.add_source_location() = source_location;
    op = verilog_lift_constant(std::move(simplified), element_type);
  };

  if(expr.id() == ID_struct && expr.type().id() == ID_struct)
  {
    auto &components = to_struct_type(expr.type()).components();
    if(components.size() == expr.operands().size())
    {
      for(std::size_t i = 0; i < components.size(); i++)
        lift_element(expr.operands()[i], components[i].type());
    }
  }
  else if(expr.id() == ID_union && expr.type().id() == ID_union)
  {
    auto &union_expr = to_union_expr(expr);
    auto &union_type = to_union_type(expr.type());
    if(union_type.has_component(union_expr.get_component_name()))
    {
      lift_element(
        union_expr.op(),
        union_type.get_component(union_expr.get_component_name()).type());
    }
  }
  else if(expr.id() == ID_array && expr.type().id() == ID_array)
  {
    auto &element_type = to_array_type(expr.type()).element_type();
    for(auto &op : expr.operands())
      lift_element(op, element_type);
  }
}

exprt verilog_constant_folding(exprt expr, const namespacet &ns)
{
  // This performs constant-folding on a type-checked expression
  // according to Section 11.2.1 IEEE 1800-2017.
  auto verilog_type = expr.type();
  auto source_location = expr.source_location();

  auto expr_lowered = verilog_lowering(std::move(expr));

  lift_aggregate_elements(expr_lowered, ns);

  // simplify
  auto expr_simplified = verilog_simplifier(std::move(expr_lowered), ns);

  // The lowering may have created new expressions without
  // source location; use the one of the original expression.
  if(expr_simplified.is_constant())
    expr_simplified.add_source_location() = source_location;

  return verilog_lift_constant(std::move(expr_simplified), verilog_type);
}
