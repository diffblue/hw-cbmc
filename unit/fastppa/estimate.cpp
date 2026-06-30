/*******************************************************************\

Module: Estimation Engine Unit Tests

Author: Kiro

\*******************************************************************/

#include <util/bitvector_types.h>
#include <util/mathematical_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <fastppa/estimate.h>
#include <fastppa/technology_db.h>
#include <testing-utils/use_catch.h>

SCENARIO("Estimation of simple next-state functions")
{
  const unsignedbv_typet u8(8);
  const unsignedbv_typet u32(32);
  technology_dbt tech("45nm");

  GIVEN("A single adder: reg' = a + b")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    word_level_transt wl_trans(ns);
    auto a = symbol_exprt{"a", u32};
    auto b = symbol_exprt{"b", u32};
    auto add = plus_exprt{a, b};
    wl_trans.next_state_functions[irep_idt("reg")] = add;

    auto reg_var = symbol_exprt{"reg", u32};
    std::vector<symbol_exprt> state_vars = {reg_var};

    // Empty transt (no invar needed for this test)
    transt trans_expr(
      ID_trans, true_exprt(), true_exprt(), true_exprt(), typet());

    auto result = estimate(wl_trans, trans_expr, state_vars, tech, ns);

    THEN("Register bits are counted")
    {
      REQUIRE(result.register_bits == 32);
      REQUIRE(result.register_area_um2 > 0);
    }

    THEN("One operator is found")
    {
      REQUIRE(result.operator_count == 1);
    }

    THEN("Critical path includes the adder delay")
    {
      REQUIRE(result.critical_path_ps > 0);
    }

    THEN("Total area includes both register and combinational")
    {
      REQUIRE(
        result.total_area_um2 ==
        Approx(result.register_area_um2 + result.combinational_area_um2));
    }
  }

  GIVEN("A chain: reg' = (a + b) * c")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    word_level_transt wl_trans(ns);
    auto a = symbol_exprt{"a", u32};
    auto b = symbol_exprt{"b", u32};
    auto c = symbol_exprt{"c", u32};
    auto add = plus_exprt{a, b};
    auto mul = mult_exprt{add, c};
    wl_trans.next_state_functions[irep_idt("reg")] = mul;

    auto reg_var = symbol_exprt{"reg", u32};
    std::vector<symbol_exprt> state_vars = {reg_var};

    transt trans_expr(
      ID_trans, true_exprt(), true_exprt(), true_exprt(), typet());

    auto result = estimate(wl_trans, trans_expr, state_vars, tech, ns);

    THEN("Two operators are found")
    {
      REQUIRE(result.operator_count == 2);
    }

    THEN("Depth is 2")
    {
      REQUIRE(result.combinational_depth == 2);
    }

    THEN("Critical path is sum of adder + multiplier delay")
    {
      auto add_cost = tech.operator_cost(ID_plus, 32);
      auto mul_cost = tech.operator_cost(ID_mult, 32);
      REQUIRE(
        result.critical_path_ps ==
        Approx(add_cost.delay_ps + mul_cost.delay_ps));
    }
  }

  GIVEN("No next-state functions (pure registers)")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    word_level_transt wl_trans(ns);
    auto reg_var = symbol_exprt{"reg", u8};
    std::vector<symbol_exprt> state_vars = {reg_var};

    transt trans_expr(
      ID_trans, true_exprt(), true_exprt(), true_exprt(), typet());

    auto result = estimate(wl_trans, trans_expr, state_vars, tech, ns);

    THEN("Only register area is reported")
    {
      REQUIRE(result.register_bits == 8);
      REQUIRE(result.combinational_area_um2 == 0);
      REQUIRE(result.operator_count == 0);
      REQUIRE(result.critical_path_ps == 0);
    }
  }
}
