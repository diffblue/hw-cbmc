/*******************************************************************\

Module: Estimation Engine Unit Tests

Author: Kiro

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/mathematical_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <fastppa/estimate.h>
#include <fastppa/technology_db.h>
#include <testing-utils/use_catch.h>

/// A transition system whose invariant is `invar` and whose init and
/// transition relation are trivial.
static transt make_trans(exprt invar = true_exprt{})
{
  return transt{
    ID_trans, std::move(invar), true_exprt{}, true_exprt{}, typet{}};
}

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

    auto result = estimate(wl_trans, trans_expr, state_vars, tech);

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

    auto result = estimate(wl_trans, trans_expr, state_vars, tech);

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

    auto result = estimate(wl_trans, make_trans(), state_vars, tech);

    THEN("Only register area is reported")
    {
      REQUIRE(result.register_bits == 8);
      REQUIRE(result.combinational_area_um2 == 0);
      REQUIRE(result.operator_count == 0);
      REQUIRE(result.critical_path_ps == 0);
    }
  }
}

SCENARIO("Zero-cost expression patterns")
{
  const unsignedbv_typet u32(32);
  technology_dbt tech("45nm");

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  auto a = symbol_exprt{"a", u32};
  auto d = symbol_exprt{"d", u32};
  auto c = symbol_exprt{"c", bool_typet{}};
  std::vector<symbol_exprt> state_vars = {symbol_exprt{"reg", u32}};

  auto estimate_nsf = [&](exprt nsf)
  {
    word_level_transt wl_trans(ns);
    wl_trans.next_state_functions[irep_idt("reg")] = std::move(nsf);
    return estimate(wl_trans, make_trans(), state_vars, tech);
  };

  GIVEN("An absorbing multiplication: reg' = a * 0")
  {
    auto result = estimate_nsf(mult_exprt{a, from_integer(0, u32)});

    THEN("The result is a constant: no logic, no path through a")
    {
      REQUIRE(result.operator_count == 0);
      REQUIRE(result.combinational_area_um2 == 0);
      REQUIRE(result.critical_path_ps == 0);
    }
  }

  GIVEN("An identity multiplication: reg' = a * 1")
  {
    auto result = estimate_nsf(mult_exprt{a, from_integer(1, u32)});

    THEN("It synthesizes to a plain wire")
    {
      REQUIRE(result.operator_count == 0);
      REQUIRE(result.combinational_area_um2 == 0);
    }
  }

  GIVEN("An identity addition: reg' = a + 0")
  {
    auto result = estimate_nsf(plus_exprt{a, from_integer(0, u32)});

    THEN("It synthesizes to a plain wire")
    {
      REQUIRE(result.operator_count == 0);
      REQUIRE(result.combinational_area_um2 == 0);
    }
  }

  GIVEN("A constant expression: reg' = 1 + 2")
  {
    auto result =
      estimate_nsf(plus_exprt{from_integer(1, u32), from_integer(2, u32)});

    THEN("It folds away entirely")
    {
      REQUIRE(result.operator_count == 0);
      REQUIRE(result.combinational_area_um2 == 0);
      REQUIRE(result.critical_path_ps == 0);
    }
  }

  GIVEN("A dead mux inside an expression: reg' = (c ? a : a) | d")
  {
    auto result = estimate_nsf(bitor_exprt{if_exprt{c, a, a}, d});

    THEN("Only the OR is costed, not the mux")
    {
      REQUIRE(result.operator_count == 1);
      REQUIRE(
        result.combinational_area_um2 ==
        Approx(tech.operator_cost(ID_bitor, 32).area_um2));
    }
  }
}

SCENARIO("Mux costing inside expressions")
{
  const unsignedbv_typet u32(32);
  technology_dbt tech("45nm");

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("A mux feeding an adder: reg' = (c ? a : b) + d")
  {
    auto c = symbol_exprt{"c", bool_typet{}};
    auto a = symbol_exprt{"a", u32};
    auto b = symbol_exprt{"b", u32};
    auto d = symbol_exprt{"d", u32};

    word_level_transt wl_trans(ns);
    wl_trans.next_state_functions[irep_idt("reg")] =
      plus_exprt{if_exprt{c, a, b}, d};
    std::vector<symbol_exprt> state_vars = {symbol_exprt{"reg", u32}};

    auto result = estimate(wl_trans, make_trans(), state_vars, tech);

    THEN(
      "The mux is costed at its full base cost: no multi-input-gate "
      "discount for its three operands")
    {
      REQUIRE(
        result.combinational_area_um2 ==
        Approx(
          tech.operator_cost(ID_if, 32).area_um2 +
          tech.operator_cost(ID_plus, 32).area_um2));
    }

    THEN("The critical path passes through mux and adder")
    {
      REQUIRE(
        result.critical_path_ps == Approx(
                                     tech.operator_cost(ID_if, 32).delay_ps +
                                     tech.operator_cost(ID_plus, 32).delay_ps));
    }
  }
}

SCENARIO("Associative-chain delay balancing")
{
  const unsignedbv_typet u32(32);
  technology_dbt tech("45nm");

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("A literal chain of four terms: reg' = ((a+b)+c)+d")
  {
    auto a = symbol_exprt{"a", u32};
    auto b = symbol_exprt{"b", u32};
    auto c = symbol_exprt{"c", u32};
    auto d = symbol_exprt{"d", u32};

    word_level_transt wl_trans(ns);
    wl_trans.next_state_functions[irep_idt("reg")] =
      plus_exprt{plus_exprt{plus_exprt{a, b}, c}, d};
    std::vector<symbol_exprt> state_vars = {symbol_exprt{"reg", u32}};

    auto result = estimate(wl_trans, make_trans(), state_vars, tech);

    THEN(
      "Delay is that of a balanced tree: log2(4) = 2 adder stages, "
      "not 3")
    {
      REQUIRE(
        result.critical_path_ps ==
        Approx(2.0 * tech.operator_cost(ID_plus, 32).delay_ps));
    }

    THEN("All three adders' area is still paid")
    {
      REQUIRE(result.operator_count == 3);
    }
  }
}

SCENARIO("Wires shared between registers")
{
  const unsignedbv_typet u32(32);
  technology_dbt tech("45nm");

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN(
    "Two registers reading one invariant-defined wire: "
    "w = a + b; reg1' = w; reg2' = w")
  {
    auto w = symbol_exprt{"w", u32};
    auto a = symbol_exprt{"a", u32};
    auto b = symbol_exprt{"b", u32};

    word_level_transt wl_trans(ns);
    wl_trans.next_state_functions[irep_idt("reg1")] = w;
    wl_trans.next_state_functions[irep_idt("reg2")] = w;
    std::vector<symbol_exprt> state_vars = {
      symbol_exprt{"reg1", u32}, symbol_exprt{"reg2", u32}};

    auto result = estimate(
      wl_trans, make_trans(equal_exprt{w, plus_exprt{a, b}}), state_vars, tech);

    THEN("The wire's adder is one piece of hardware, costed once")
    {
      REQUIRE(result.operator_count == 1);
      REQUIRE(
        result.combinational_area_um2 ==
        Approx(tech.operator_cost(ID_plus, 32).area_um2));
    }

    THEN("Both registers still see the adder's delay")
    {
      REQUIRE(
        result.critical_path_ps ==
        Approx(tech.operator_cost(ID_plus, 32).delay_ps));
    }
  }
}

SCENARIO("Register array costing")
{
  const unsignedbv_typet u32(32);
  technology_dbt tech("45nm");

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  word_level_transt wl_trans(ns);

  GIVEN("An array above the SRAM threshold: 256 x 32 = 8192 bits")
  {
    auto mem =
      symbol_exprt{"mem", array_typet{u32, from_integer(256, integer_typet{})}};
    std::vector<symbol_exprt> state_vars = {mem};

    auto result = estimate(wl_trans, make_trans(), state_vars, tech);

    THEN("It is costed at SRAM density, 1 um2/bit")
    {
      REQUIRE(result.register_bits == 8192);
      REQUIRE(result.register_area_um2 == Approx(8192.0));
    }
  }

  GIVEN("An array below the SRAM threshold: 32 x 32 = 1024 bits")
  {
    auto mem =
      symbol_exprt{"mem", array_typet{u32, from_integer(32, integer_typet{})}};
    std::vector<symbol_exprt> state_vars = {mem};

    auto result = estimate(wl_trans, make_trans(), state_vars, tech);

    THEN("It is costed as flip-flops")
    {
      REQUIRE(result.register_bits == 1024);
      REQUIRE(
        result.register_area_um2 == Approx(tech.register_cost(1024).area_um2));
    }
  }
}
