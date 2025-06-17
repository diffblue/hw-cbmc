/*******************************************************************\

Module: SVA Sequence Matches

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/mathematical_types.h>

#include <temporal-logic/sva_sequence_match.h>
#include <testing-utils/use_catch.h>
#include <verilog/sva_expr.h>

SCENARIO("Generating the matches for an SVA sequence")
{
  const auto sequence_type = verilog_sva_sequence_typet{};

  GIVEN("A boolean formula")
  {
    auto p = symbol_exprt{"p", bool_typet{}};

    REQUIRE(
      LTL_sequence_matches(sva_boolean_exprt{p, sequence_type}) ==
      std::vector<sva_sequence_matcht>{sva_sequence_matcht{p}});
  }

  GIVEN("##1 p")
  {
    auto p = symbol_exprt{"p", bool_typet{}};
    auto one = from_integer(1, integer_typet{});

    REQUIRE(
      LTL_sequence_matches(
        sva_cycle_delay_exprt{one, sva_boolean_exprt{p, sequence_type}}) ==
      std::vector<sva_sequence_matcht>{sva_sequence_matcht{{true_exprt{}, p}}});
  }

  GIVEN("##[*] p")
  {
    auto p = symbol_exprt{"p", bool_typet{}};

    CHECK_THROWS_AS(
      LTL_sequence_matches(
        sva_cycle_delay_star_exprt{sva_boolean_exprt{p, sequence_type}}),
      sva_sequence_match_unsupportedt);
  }
}
