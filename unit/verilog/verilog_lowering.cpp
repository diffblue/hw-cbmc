/*******************************************************************\

Module: Verilog Lowering Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <util/floatbv_expr.h>
#include <util/ieee_float.h>
#include <util/std_expr.h>

#include <testing-utils/use_catch.h>
#include <verilog/verilog_lowering.h>
#include <verilog/verilog_types.h>

/// helper: a constant of the given Verilog real type, with the value
/// encoded as for the back-ends
static constant_exprt real_constant(double value, const typet &type)
{
  ieee_float_valuet f{ieee_float_spect::double_precision()};
  if(type.id() == ID_verilog_shortreal)
    f = ieee_float_valuet{ieee_float_spect::single_precision()};
  f.from_double(value);
  return constant_exprt{f.to_expr().get_value(), type};
}

static const exprt round_to_even =
  ieee_floatt::rounding_mode_expr(ieee_floatt::rounding_modet::ROUND_TO_EVEN);

SCENARIO("verilog_lowering lowers real arithmetic to IEEE 754 operations")
{
  auto real = verilog_real_typet{};
  auto floatbv = verilog_lowering(real);
  auto a = real_constant(1.5, real);
  auto b = real_constant(2.0, real);
  auto c = real_constant(4.0, real);

  GIVEN("binary arithmetic on reals")
  {
    const std::pair<exprt, irep_idt> cases[] = {
      {plus_exprt{a, b}, ID_floatbv_plus},
      {minus_exprt{a, b}, ID_floatbv_minus},
      {mult_exprt{a, b}, ID_floatbv_mult},
      {div_exprt{a, b}, ID_floatbv_div}};

    for(auto &[expr, id] : cases)
    {
      THEN("the result is " + id2string(id) + " with round-to-even")
      {
        auto result = verilog_lowering(expr);
        REQUIRE(result.id() == id);
        REQUIRE(result.type() == floatbv);
        auto &op = to_ieee_float_op_expr(result);
        REQUIRE(op.lhs() == verilog_lowering(a));
        REQUIRE(op.rhs() == verilog_lowering(b));
        REQUIRE(op.rounding_mode() == round_to_even);
      }
    }
  }

  GIVEN("a sum with three operands")
  {
    plus_exprt expr{a, b};
    expr.add_to_operands(c);

    THEN("the operands are added left to right")
    {
      auto result = verilog_lowering(expr);
      REQUIRE(result.id() == ID_floatbv_plus);
      auto &outer = to_ieee_float_op_expr(result);
      REQUIRE(outer.rhs() == verilog_lowering(c));
      REQUIRE(outer.lhs().id() == ID_floatbv_plus);
      auto &inner = to_ieee_float_op_expr(outer.lhs());
      REQUIRE(inner.lhs() == verilog_lowering(a));
      REQUIRE(inner.rhs() == verilog_lowering(b));
    }
  }

  GIVEN("shortreal arithmetic")
  {
    auto shortreal = verilog_shortreal_typet{};
    plus_exprt expr{
      real_constant(1.5, shortreal), real_constant(2.0, shortreal)};

    THEN("the result is single precision")
    {
      auto result = verilog_lowering(expr);
      REQUIRE(result.id() == ID_floatbv_plus);
      REQUIRE(result.type() == verilog_lowering(shortreal));
      REQUIRE(to_floatbv_type(result.type()).get_width() == 32);
    }
  }
}

SCENARIO("verilog_lowering lowers the type of a conditional on reals")
{
  auto real = verilog_real_typet{};
  auto a = real_constant(1.5, real);
  auto b = real_constant(2.5, real);
  symbol_exprt cond{"c", bool_typet{}};

  GIVEN("a conditional with real operands")
  {
    if_exprt expr{cond, a, b, real};

    THEN("the conditional and its operands have the floatbv type")
    {
      auto result = verilog_lowering(expr);
      REQUIRE(result.id() == ID_if);
      REQUIRE(result.type() == verilog_lowering(real));
      REQUIRE(to_if_expr(result).true_case() == verilog_lowering(a));
      REQUIRE(to_if_expr(result).false_case() == verilog_lowering(b));
    }
  }
}
