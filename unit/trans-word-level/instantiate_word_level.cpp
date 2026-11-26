/*******************************************************************\

Module: Instantiate Word-Level Expressions

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>

#include <testing-utils/use_catch.h>
#include <trans-word-level/instantiate_word_level.h>
#include <trans-word-level/next_symbol.h>
#include <verilog/verilog_expr.h>

SCENARIO("Instantiating word-level expressions")
{
  const mp_integer no_timeframes = 10;
  auto x = symbol_exprt{"x", bool_typet{}};
  auto y = symbol_exprt{"y", bool_typet{}};

  GIVEN("Symbols")
  {
    REQUIRE(
      instantiate(x, 3, no_timeframes) == symbol_exprt{"x@3", bool_typet{}});
    REQUIRE(timeframe_identifier(3, "x") == "x@3");
    REQUIRE(
      instantiate(next_symbol_exprt{x}, 3, no_timeframes) ==
      symbol_exprt{"x@4", bool_typet{}});
    REQUIRE(
      instantiate_state_predicate(and_exprt{x, y}, 0, no_timeframes) ==
      and_exprt{
        symbol_exprt{"x@0", bool_typet{}}, symbol_exprt{"y@0", bool_typet{}}});
  }

  GIVEN("A nondet_symbol")
  {
    auto n = nondet_symbol_exprt{"n", bool_typet{}};
    REQUIRE(
      instantiate(n, 2, no_timeframes) ==
      nondet_symbol_exprt{"nondet::n@2", bool_typet{}});
  }

  GIVEN("A symbol and a next_symbol with the same identifier")
  {
    auto expr = equal_exprt{next_symbol_exprt{x}, not_exprt{x}};
    REQUIRE(
      instantiate(expr, 5, no_timeframes) ==
      equal_exprt{
        symbol_exprt{"x@6", bool_typet{}},
        not_exprt{symbol_exprt{"x@5", bool_typet{}}}});
  }

  GIVEN("Symbols with the same identifier but different types")
  {
    auto x8 = symbol_exprt{"x", unsignedbv_typet{8}};
    auto x16 = symbol_exprt{"x", unsignedbv_typet{16}};
    auto expr = and_exprt{
      equal_exprt{x8, x8}, equal_exprt{x16, x16}, equal_exprt{x8, x8}};
    auto result = instantiate(expr, 1, no_timeframes);
    REQUIRE(
      result == and_exprt{
                  equal_exprt{
                    symbol_exprt{"x@1", unsignedbv_typet{8}},
                    symbol_exprt{"x@1", unsignedbv_typet{8}}},
                  equal_exprt{
                    symbol_exprt{"x@1", unsignedbv_typet{16}},
                    symbol_exprt{"x@1", unsignedbv_typet{16}}},
                  equal_exprt{
                    symbol_exprt{"x@1", unsignedbv_typet{8}},
                    symbol_exprt{"x@1", unsignedbv_typet{8}}}});
  }

  GIVEN("$past")
  {
    auto past = verilog_past_exprt{x, from_integer(2, integer_typet{})};
    REQUIRE(
      instantiate(past, 3, no_timeframes) == symbol_exprt{"x@1", bool_typet{}});
    REQUIRE(instantiate(past, 1, no_timeframes) == past.default_value());

    // the same $past expression in two places
    auto expr = and_exprt{past, past};
    REQUIRE(
      instantiate(expr, 2, no_timeframes) ==
      and_exprt{
        symbol_exprt{"x@0", bool_typet{}}, symbol_exprt{"x@0", bool_typet{}}});
  }

  GIVEN("An expression without symbols")
  {
    auto expr = and_exprt{true_exprt{}, not_exprt{false_exprt{}}};
    auto result = instantiate(expr, 4, no_timeframes);
    REQUIRE(result == expr);
    // the expression is not copied
    REQUIRE(&result.read() == &expr.read());
  }

  GIVEN("An expression with a shared subexpression")
  {
    exprt shared = or_exprt{x, not_exprt{y}};
    auto expr = and_exprt{shared, shared};
    auto result = instantiate(expr, 7, no_timeframes);
    auto expected = or_exprt{
      symbol_exprt{"x@7", bool_typet{}},
      not_exprt{symbol_exprt{"y@7", bool_typet{}}}};
    REQUIRE(result == and_exprt{expected, expected});
    // the instance is shared as well
    REQUIRE(
      &to_and_expr(result).op0().read() == &to_and_expr(result).op1().read());
  }
}
