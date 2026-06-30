/*******************************************************************\

Module: Technology Database Unit Tests

Author: Kiro

\*******************************************************************/

#include <fastppa/technology_db.h>
#include <testing-utils/use_catch.h>

SCENARIO("Technology database cost scaling")
{
  GIVEN("A 45nm technology database")
  {
    technology_dbt tech("45nm");

    THEN("Adder area scales linearly with width")
    {
      auto cost8 = tech.operator_cost(ID_plus, 8);
      auto cost32 = tech.operator_cost(ID_plus, 32);
      REQUIRE(cost32.area_um2 > cost8.area_um2);
      REQUIRE(cost32.area_um2 == Approx(cost8.area_um2 * 4.0));
    }

    THEN("Multiplier area scales quadratically with width")
    {
      auto cost8 = tech.operator_cost(ID_mult, 8);
      auto cost16 = tech.operator_cost(ID_mult, 16);
      // area_per_bit = 5*n, so total = 5*n*n
      // cost16/cost8 = (5*16*16) / (5*8*8) = 4
      REQUIRE(cost16.area_um2 == Approx(cost8.area_um2 * 4.0));
    }

    THEN("Bitwise ops have constant delay regardless of width")
    {
      auto cost8 = tech.operator_cost(ID_bitand, 8);
      auto cost64 = tech.operator_cost(ID_bitand, 64);
      REQUIRE(cost8.delay_ps == cost64.delay_ps);
    }

    THEN("Concatenation has zero cost")
    {
      auto cost = tech.operator_cost(ID_concatenation, 32);
      REQUIRE(cost.area_um2 == 0);
      REQUIRE(cost.delay_ps == 0);
      REQUIRE(cost.energy_fj == 0);
    }

    THEN("Register cost scales linearly")
    {
      auto cost1 = tech.register_cost(1);
      auto cost32 = tech.register_cost(32);
      REQUIRE(cost32.area_um2 == Approx(cost1.area_um2 * 32.0));
    }
  }

  GIVEN("Different process nodes")
  {
    technology_dbt tech7("7nm");
    technology_dbt tech45("45nm");
    technology_dbt tech130("130nm");

    THEN("7nm is smaller than 45nm")
    {
      auto a7 = tech7.operator_cost(ID_plus, 32);
      auto a45 = tech45.operator_cost(ID_plus, 32);
      REQUIRE(a7.area_um2 < a45.area_um2);
      REQUIRE(a7.delay_ps < a45.delay_ps);
    }

    THEN("130nm is larger than 45nm")
    {
      auto a45 = tech45.operator_cost(ID_plus, 32);
      auto a130 = tech130.operator_cost(ID_plus, 32);
      REQUIRE(a130.area_um2 > a45.area_um2);
      REQUIRE(a130.delay_ps > a45.delay_ps);
    }
  }

  GIVEN("An invalid process node")
  {
    THEN("Construction throws")
    {
      REQUIRE_THROWS(technology_dbt("2nm"));
    }
  }
}
