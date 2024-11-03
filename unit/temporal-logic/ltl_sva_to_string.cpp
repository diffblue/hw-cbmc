/*******************************************************************\

Module: Property Instrumentation via Buechi Automata

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <temporal-logic/ltl.h>
#include <temporal-logic/ltl_sva_to_string.h>
#include <testing-utils/use_catch.h>

SCENARIO("Generating a string from a formula")
{
  GIVEN("A formula")
  {
    auto p = symbol_exprt{"p", bool_typet{}};
    auto q = symbol_exprt{"q", bool_typet{}};
    REQUIRE(ltl_sva_to_stringt{}(p).s == "a");
    REQUIRE(ltl_sva_to_stringt{}(not_exprt{G_exprt{p}}).s == "!Ga");
    REQUIRE(ltl_sva_to_stringt{}(X_exprt{F_exprt{p}}).s == "XFa");
    REQUIRE(ltl_sva_to_stringt{}(U_exprt{X_exprt{p}, q}).s == "(Xa)Ub");
    REQUIRE(ltl_sva_to_stringt{}(U_exprt{p, q}).s == "aUb");
    REQUIRE(ltl_sva_to_stringt{}(and_exprt{p, q}).s == "a&b");
  }
}
