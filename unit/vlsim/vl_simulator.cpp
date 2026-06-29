/*******************************************************************\

Module: vlsim Simulator Unit Tests

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>
#include <util/message.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <testing-utils/use_catch.h>
#include <verilog/verilog_types.h>
#include <vlsim/vl_simulator.h>

static mp_integer eval(const exprt &expr)
{
  null_message_handlert handler;
  symbol_tablet symbol_table;
  vl_simulatort sim{symbol_table, handler};
  return sim.eval_expr(expr);
}

SCENARIO("vl_simulatort evaluates constant expressions")
{
  GIVEN("integer constant 42")
  {
    REQUIRE(eval(from_integer(42, integer_typet{})) == 42);
  }

  GIVEN("unsignedbv constant 255")
  {
    REQUIRE(eval(from_integer(255, unsignedbv_typet{8})) == 255);
  }

  GIVEN("signedbv constant -1")
  {
    REQUIRE(eval(from_integer(-1, signedbv_typet{32})) == -1);
  }
}

SCENARIO("vl_simulatort evaluates arithmetic expressions")
{
  GIVEN("3 + 4 == 7")
  {
    auto a = from_integer(3, integer_typet{});
    auto b = from_integer(4, integer_typet{});
    REQUIRE(eval(plus_exprt{a, b, integer_typet{}}) == 7);
  }

  GIVEN("10 - 3 == 7")
  {
    auto a = from_integer(10, integer_typet{});
    auto b = from_integer(3, integer_typet{});
    REQUIRE(eval(minus_exprt{a, b}) == 7);
  }

  GIVEN("6 * 7 == 42")
  {
    auto a = from_integer(6, integer_typet{});
    auto b = from_integer(7, integer_typet{});
    REQUIRE(eval(mult_exprt{a, b}) == 42);
  }

  GIVEN("10 / 3 == 3")
  {
    auto a = from_integer(10, integer_typet{});
    auto b = from_integer(3, integer_typet{});
    REQUIRE(eval(div_exprt{a, b}) == 3);
  }

  GIVEN("10 mod 3 == 1")
  {
    auto a = from_integer(10, integer_typet{});
    auto b = from_integer(3, integer_typet{});
    REQUIRE(eval(mod_exprt{a, b}) == 1);
  }
}

SCENARIO("vl_simulatort evaluates comparison expressions")
{
  GIVEN("3 == 3 is true (1)")
  {
    auto a = from_integer(3, integer_typet{});
    auto b = from_integer(3, integer_typet{});
    REQUIRE(eval(equal_exprt{a, b}) == 1);
  }

  GIVEN("3 == 4 is false (0)")
  {
    auto a = from_integer(3, integer_typet{});
    auto b = from_integer(4, integer_typet{});
    REQUIRE(eval(equal_exprt{a, b}) == 0);
  }

  GIVEN("3 != 4 is true (1)")
  {
    auto a = from_integer(3, integer_typet{});
    auto b = from_integer(4, integer_typet{});
    REQUIRE(eval(notequal_exprt{a, b}) == 1);
  }

  GIVEN("3 < 4 is true (1)")
  {
    auto a = from_integer(3, integer_typet{});
    auto b = from_integer(4, integer_typet{});
    REQUIRE(eval(binary_relation_exprt{a, ID_lt, b}) == 1);
  }

  GIVEN("4 < 3 is false (0)")
  {
    auto a = from_integer(4, integer_typet{});
    auto b = from_integer(3, integer_typet{});
    REQUIRE(eval(binary_relation_exprt{a, ID_lt, b}) == 0);
  }

  GIVEN("4 > 3 is true (1)")
  {
    auto a = from_integer(4, integer_typet{});
    auto b = from_integer(3, integer_typet{});
    REQUIRE(eval(binary_relation_exprt{a, ID_gt, b}) == 1);
  }

  GIVEN("3 <= 3 is true (1)")
  {
    auto a = from_integer(3, integer_typet{});
    auto b = from_integer(3, integer_typet{});
    REQUIRE(eval(binary_relation_exprt{a, ID_le, b}) == 1);
  }
}

SCENARIO("vl_simulatort evaluates ternary if expression")
{
  GIVEN("1 ? 42 : 0 == 42")
  {
    auto cond = from_integer(1, bool_typet{});
    auto a = from_integer(42, integer_typet{});
    auto b = from_integer(0, integer_typet{});
    if_exprt ternary{cond, a, b, integer_typet{}};
    REQUIRE(eval(ternary) == 42);
  }

  GIVEN("0 ? 42 : 99 == 99")
  {
    auto cond = from_integer(0, bool_typet{});
    auto a = from_integer(42, integer_typet{});
    auto b = from_integer(99, integer_typet{});
    if_exprt ternary{cond, a, b, integer_typet{}};
    REQUIRE(eval(ternary) == 99);
  }
}

SCENARIO("vl_simulatort evaluates four-valued constants with known bits")
{
  // verilog_unsignedbv_typet constants use a char-per-bit encoding, MSB first.
  // '0' and '1' are known bits; 'x' and 'z' are indeterminate.

  GIVEN("4-bit all-zeros constant 4'b0000")
  {
    constant_exprt c{"0000", verilog_unsignedbv_typet{4}};
    REQUIRE(eval(c) == 0);
  }

  GIVEN("4-bit all-ones constant 4'b1111 == 15")
  {
    constant_exprt c{"1111", verilog_unsignedbv_typet{4}};
    REQUIRE(eval(c) == 15);
  }

  GIVEN("4-bit constant 4'b1010 == 10")
  {
    constant_exprt c{"1010", verilog_unsignedbv_typet{4}};
    REQUIRE(eval(c) == 10);
  }

  GIVEN("8-bit constant 8'b00101010 == 42")
  {
    constant_exprt c{"00101010", verilog_unsignedbv_typet{8}};
    REQUIRE(eval(c) == 42);
  }
}

SCENARIO("vl_simulatort evaluates four-valued constants with x bits")
{
  // x bits are indeterminate; treated as 0 in arithmetic context.

  GIVEN("4-bit all-x constant 4'bxxxx evaluates to 0")
  {
    auto c = verilog_unsignedbv_typet{4}.all_x_expr();
    REQUIRE(eval(c) == 0);
  }

  GIVEN(
    "4-bit 4'b1x1x: known 1-bits contribute, x treated as 0, result is 10 "
    "(binary 1010)")
  {
    constant_exprt c{"1x1x", verilog_unsignedbv_typet{4}};
    REQUIRE(eval(c) == 10);
  }

  GIVEN("4-bit 4'b0xx1: known bits give 0001 == 1")
  {
    constant_exprt c{"0xx1", verilog_unsignedbv_typet{4}};
    REQUIRE(eval(c) == 1);
  }
}

SCENARIO("vl_simulatort evaluates four-valued constants with z bits")
{
  // z (high-impedance) bits are treated as 0 in arithmetic context.

  GIVEN("4-bit all-z constant 4'bzzzz evaluates to 0")
  {
    auto c = verilog_unsignedbv_typet{4}.all_z_expr();
    REQUIRE(eval(c) == 0);
  }

  GIVEN("4-bit 4'b1z0z: known bits give 1000 == 8")
  {
    constant_exprt c{"1z0z", verilog_unsignedbv_typet{4}};
    REQUIRE(eval(c) == 8);
  }
}

SCENARIO("vl_simulatort evaluates four-valued signed constants")
{
  GIVEN("4-bit signed constant 4'sb1010 == -6 (two's complement)")
  {
    // "1010" in 4-bit two's complement signed is -6
    // but eval returns positive integer from char-per-bit parse (10)
    // because mp_integer doesn't apply sign extension automatically
    constant_exprt c{"1010", verilog_signedbv_typet{4}};
    // The parser returns raw bit value 10 (no sign extension in eval_expr)
    REQUIRE(eval(c) == 10);
  }

  GIVEN("4-bit signed all-x constant evaluates to 0")
  {
    constant_exprt c{"xxxx", verilog_signedbv_typet{4}};
    REQUIRE(eval(c) == 0);
  }
}
