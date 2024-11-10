/*******************************************************************\

Module: NNF Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <temporal-logic/ltl.h>
#include <temporal-logic/nnf.h>
#include <testing-utils/use_catch.h>

SCENARIO("Generating NNF")
{
  GIVEN("A formula not in NNF")
  {
    auto p = symbol_exprt{"p", bool_typet{}};
    auto formula = not_exprt{G_exprt{p}};
    REQUIRE(property_nnf(formula) == F_exprt{not_exprt{p}});
  }
}
