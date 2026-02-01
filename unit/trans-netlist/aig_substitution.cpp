/*******************************************************************\

Module: AIG Substitution Map Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <trans-netlist/aig_substitution.h>

SCENARIO("aig_substitution_mapt construction")
{
  GIVEN("A substitution map of size 3")
  {
    aig_substitution_mapt map(3);

    THEN("size returns the number of entries")
    {
      REQUIRE(map.size() == 3);
    }
  }
}

SCENARIO("aig_substitution_mapt operator()")
{
  GIVEN("A substitution map with entries")
  {
    aig_substitution_mapt map(3);
    map[0] = literalt(10, false);
    map[1] = literalt(20, true);
    map[2] = literalt(30, false);

    THEN("applying to a positive literal returns the mapped literal")
    {
      REQUIRE(map(literalt(0, false)) == literalt(10, false));
      REQUIRE(map(literalt(1, false)) == literalt(20, true));
      REQUIRE(map(literalt(2, false)) == literalt(30, false));
    }

    THEN("applying to a negated literal flips the sign of the result")
    {
      REQUIRE(map(literalt(0, true)) == literalt(10, true));
      REQUIRE(map(literalt(1, true)) == literalt(20, false));
      REQUIRE(map(literalt(2, true)) == literalt(30, true));
    }

    THEN("applying to constant true returns constant true")
    {
      REQUIRE(map(const_literal(true)) == const_literal(true));
    }

    THEN("applying to constant false returns constant false")
    {
      REQUIRE(map(const_literal(false)) == const_literal(false));
    }
  }
}

SCENARIO("aig_substitution_mapt operator[]")
{
  GIVEN("A substitution map of size 2")
  {
    aig_substitution_mapt map(2);
    map[0] = literalt(5, false);
    map[1] = literalt(6, true);

    THEN("const operator[] reads back the stored literals")
    {
      const auto &cmap = map;
      REQUIRE(cmap[0] == literalt(5, false));
      REQUIRE(cmap[1] == literalt(6, true));
    }
  }
}
