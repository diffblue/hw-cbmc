/*******************************************************************\

Module: Property Instrumentation via Buechi Automata

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/mathematical_types.h>

#include <temporal-logic/ltl.h>
#include <temporal-logic/ltl_sva_to_string.h>
#include <testing-utils/use_catch.h>
#include <verilog/sva_expr.h>

SCENARIO("Generating a string from a formula")
{
  GIVEN("A boolean formula")
  {
    auto p = symbol_exprt{"p", bool_typet{}};
    auto q = symbol_exprt{"q", bool_typet{}};

    REQUIRE(ltl_sva_to_stringt{}(true_exprt{}) == "true");
    REQUIRE(ltl_sva_to_stringt{}(p) == "a0");
    REQUIRE(ltl_sva_to_stringt{}(and_exprt{p, q}) == "a0&a1");
  }

  GIVEN("An LTL formula")
  {
    auto p = symbol_exprt{"p", bool_typet{}};
    auto q = symbol_exprt{"q", bool_typet{}};

    REQUIRE(ltl_sva_to_stringt{}(not_exprt{G_exprt{p}}) == "!Ga0");
    REQUIRE(ltl_sva_to_stringt{}(X_exprt{F_exprt{p}}) == "XFa0");
    REQUIRE(ltl_sva_to_stringt{}(U_exprt{X_exprt{p}, q}) == "(Xa0) U a1");
    REQUIRE(ltl_sva_to_stringt{}(U_exprt{p, q}) == "a0 U a1");
  }

  GIVEN("An SVA formula")
  {
    auto sequence_type = verilog_sva_sequence_typet{};
    auto p = sva_boolean_exprt{symbol_exprt{"p", bool_typet{}}, sequence_type};
    auto q = sva_boolean_exprt{symbol_exprt{"q", bool_typet{}}, sequence_type};

    auto sequence = [](const exprt &expr) {
      return ltl_sva_to_stringt{}(sva_weak_exprt{ID_sva_weak, expr});
    };

    REQUIRE(
      sequence(sva_cycle_delay_exprt{from_integer(1, natural_typet{}), p}) ==
      "{1[*1] ; a0}");

    REQUIRE(
      sequence(sva_sequence_concatenation_exprt{
        p, sva_cycle_delay_exprt{from_integer(0, natural_typet{}), q}}) ==
      "{a0 : a1}");

    REQUIRE(
      sequence(sva_sequence_concatenation_exprt{
        p, sva_cycle_delay_exprt{from_integer(1, natural_typet{}), q}}) ==
      "{a0 ; a1}");

    REQUIRE(
      sequence(sva_sequence_concatenation_exprt{
        p, sva_cycle_delay_exprt{from_integer(10, natural_typet{}), q}}) ==
      "{a0 ; 1[*9] ; a1}");
  }
}
