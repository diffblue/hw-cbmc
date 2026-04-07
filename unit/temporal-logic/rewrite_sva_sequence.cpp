/*******************************************************************\

Module: Rewrite SVA Sequences

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/mathematical_types.h>

#include <temporal-logic/rewrite_sva_sequence.h>
#include <testing-utils/use_catch.h>
#include <verilog/sva_expr.h>

SCENARIO("Checking whether an SVA sequence admits an empty match")
{
  auto p = sva_boolean_exprt{
    symbol_exprt{"p", bool_typet{}}, verilog_sva_sequence_typet{}};
  auto q = sva_boolean_exprt{
    symbol_exprt{"q", bool_typet{}}, verilog_sva_sequence_typet{}};

  GIVEN("A boolean formula")
  {
    REQUIRE(admits_empty(p) == false);
  }

  GIVEN("p ##0 q")
  {
    auto seq = sva_cycle_delay_exprt{p, from_integer(0, natural_typet{}), q};
    REQUIRE(admits_empty(seq) == false);
  }

  GIVEN("p[+]")
  {
    auto seq = sva_sequence_repetition_plus_exprt{p}.lower();
    REQUIRE(admits_empty(seq) == false);
  }

  GIVEN("p[*]")
  {
    auto seq = sva_sequence_repetition_star_exprt{p};
    REQUIRE(admits_empty(seq) == true);
  }
}
