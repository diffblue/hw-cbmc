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
      // area_per_bit is linear in n, so total area is quadratic:
      // cost16/cost8 = 16*16 / (8*8) = 4
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

    THEN("Zero width is clamped to one bit")
    {
      auto cost0 = tech.operator_cost(ID_plus, 0);
      auto cost1 = tech.operator_cost(ID_plus, 1);
      REQUIRE(cost0.area_um2 == Approx(cost1.area_um2));
      REQUIRE(cost0.delay_ps == Approx(cost1.delay_ps));
    }

    THEN(
      "Unary minus has the same delay as an adder: both are "
      "structurally one adder")
    {
      REQUIRE(
        tech.operator_cost(ID_unary_minus, 32).delay_ps ==
        Approx(tech.operator_cost(ID_plus, 32).delay_ps));
    }

    THEN("div and mod share one cost model, superlinear in width")
    {
      auto div16 = tech.operator_cost(ID_div, 16);
      auto div32 = tech.operator_cost(ID_div, 32);
      auto mod32 = tech.operator_cost(ID_mod, 32);
      REQUIRE(div32.area_um2 == Approx(mod32.area_um2));
      REQUIRE(div32.delay_ps == Approx(mod32.delay_ps));
      // delay ~ n^1.89: doubling the width far more than doubles it
      REQUIRE(div32.delay_ps > 2.0 * div16.delay_ps);
    }

    THEN("Mux cost charges one stage per decode level")
    {
      auto mux2 = tech.mux_cost(8, 2); // 1 level
      auto mux8 = tech.mux_cost(8, 8); // 3 levels
      REQUIRE(mux8.delay_ps == Approx(3.0 * mux2.delay_ps));
      REQUIRE(mux8.area_um2 == Approx(3.0 * mux2.area_um2));
    }

    THEN("The if-then-else operator is the calibrated single mux stage")
    {
      // The 0.7 is the former multi-input-gate correction, which used to
      // hit every three-operand if-then-else and is now folded into the
      // operator's base cost (see technology_db.cpp).
      auto if_cost = tech.operator_cost(ID_if, 8);
      auto mux2 = tech.mux_cost(8, 2);
      REQUIRE(if_cost.area_um2 == Approx(0.7 * mux2.area_um2));
      REQUIRE(if_cost.energy_fj == Approx(0.7 * mux2.energy_fj));
      REQUIRE(if_cost.delay_ps == Approx(mux2.delay_ps));
    }

    THEN("A sparse constant multiplier is cheaper than a full multiplier")
    {
      auto by_constant = tech.constant_mult_cost(32, 1); // one set bit
      auto full = tech.operator_cost(ID_mult, 32);
      REQUIRE(by_constant.area_um2 < full.area_um2);
      REQUIRE(by_constant.delay_ps < full.delay_ps);
    }

    THEN("Array read cost grows with array size, and size 1 is clamped")
    {
      auto idx1 = tech.index_cost(8, 1);
      auto idx2 = tech.index_cost(8, 2);
      auto idx32 = tech.index_cost(8, 32);
      REQUIRE(idx1.area_um2 == Approx(idx2.area_um2));
      REQUIRE(idx1.delay_ps == Approx(idx2.delay_ps));
      REQUIRE(idx32.area_um2 > idx2.area_um2);
      REQUIRE(idx32.delay_ps > idx2.delay_ps);
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

  GIVEN("Every advertised process node")
  {
    THEN("All of them construct")
    {
      for(const auto &node :
          {"3nm", "7nm", "14nm", "28nm", "45nm", "65nm", "90nm", "130nm"})
      {
        REQUIRE_NOTHROW(technology_dbt{node});
      }
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
