/*******************************************************************\

Module: SVA to LTL

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/std_expr.h>

#include <temporal-logic/sva_to_ltl.h>
#include <testing-utils/use_catch.h>

SCENARIO("Generating LTL from SVA")
{
  GIVEN("A boolean formula")
  {
    auto p = symbol_exprt{"p", bool_typet{}};
    auto q = symbol_exprt{"q", bool_typet{}};

    REQUIRE(SVA_to_LTL(true_exprt{}) == true_exprt{});
    REQUIRE(SVA_to_LTL(p) == p);
    REQUIRE(SVA_to_LTL(equal_exprt{p, q}) == equal_exprt{p, q});
  }
}
