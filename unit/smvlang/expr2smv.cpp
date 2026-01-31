/*******************************************************************\

Module: expr2smv Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <smvlang/expr2smv.h>
#include <temporal-logic/ctl.h>
#include <testing-utils/use_catch.h>

SCENARIO("Generating SMV expression strings")
{
  const symbol_tablet symbol_table;
  const namespacet empty_ns{symbol_table};

  GIVEN("An expression with non-associative operators")
  {
    auto t = integer_typet{};
    auto n = [t](mp_integer i) { return from_integer(i, t); };
    auto expr = div_exprt{n(3), div_exprt{n(4), n(2)}};
    REQUIRE(expr2smv(expr, empty_ns) == "3 / (4 / 2)");
  }

  GIVEN("An expression with associative operators")
  {
    auto t = integer_typet{};
    auto n = [t](mp_integer i) { return from_integer(i, t); };
    auto expr = plus_exprt{n(3), plus_exprt{n(4), n(2)}};
    REQUIRE(expr2smv(expr, empty_ns) == "3 + 4 + 2");
  }

  GIVEN("A binary CTL operator")
  {
    auto expr = AU_exprt{true_exprt(), false_exprt()};
    REQUIRE(expr2smv(expr, empty_ns) == "A [TRUE U FALSE]");
  }
}
