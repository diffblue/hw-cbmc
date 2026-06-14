/*******************************************************************\

Module: convert_literals Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <verilog/convert_literals.h>
#include <verilog/verilog_expr.h>
#include <verilog/verilog_types.h>

SCENARIO("based unsized literals")
{
  GIVEN("'hx0")
  {
    auto expr = convert_integral_literal("'hx0");
    REQUIRE(expr.id() == ID_verilog_based_unsized_literal);
    auto &lit = to_verilog_based_unsized_literal_expr(expr);
    REQUIRE(lit.value() == "xxxx0000");
    REQUIRE(lit.type() == verilog_unsignedbv_typet{32});
  }

  GIVEN("'hz0")
  {
    auto expr = convert_integral_literal("'hz0");
    REQUIRE(expr.id() == ID_verilog_based_unsized_literal);
    auto &lit = to_verilog_based_unsized_literal_expr(expr);
    REQUIRE(lit.value() == "zzzz0000");
  }

  GIVEN("'hFF — MSB is not x/z")
  {
    auto expr = convert_integral_literal("'hFF");
    REQUIRE(expr.id() == ID_verilog_based_unsized_literal);
    auto &lit = to_verilog_based_unsized_literal_expr(expr);
    REQUIRE(lit.value() == "11111111");
    REQUIRE(lit.type() == unsignedbv_typet{32});
  }

  GIVEN("'bx — single x bit")
  {
    auto expr = convert_integral_literal("'bx");
    REQUIRE(expr.id() == ID_verilog_based_unsized_literal);
    auto &lit = to_verilog_based_unsized_literal_expr(expr);
    REQUIRE(lit.value() == "x");
    REQUIRE(lit.type() == verilog_unsignedbv_typet{32});
  }

  GIVEN("'sb1 — signed based unsized")
  {
    auto expr = convert_integral_literal("'sb1");
    REQUIRE(expr.id() == ID_verilog_based_unsized_literal);
    auto &lit = to_verilog_based_unsized_literal_expr(expr);
    REQUIRE(lit.value() == "1");
    REQUIRE(lit.type() == signedbv_typet{32});
  }

  GIVEN("'dx — decimal x")
  {
    auto expr = convert_integral_literal("'dx");
    REQUIRE(expr.id() == ID_verilog_based_unsized_literal);
    auto &lit = to_verilog_based_unsized_literal_expr(expr);
    REQUIRE(lit.type() == verilog_unsignedbv_typet{32});
    REQUIRE(lit.value() == std::string(32, 'x'));
  }
}
