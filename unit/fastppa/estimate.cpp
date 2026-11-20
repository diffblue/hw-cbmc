/*******************************************************************\

Module: Estimation Engine Unit Tests

Author: Kiro

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/mathematical_expr.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <ebmc/ebmc_error.h>
#include <fastppa/cost_table.h>
#include <fastppa/estimate.h>
#include <fastppa/technology_db.h>
#include <testing-utils/use_catch.h>

#include <sstream>

namespace
{
/// Costs chosen so that every expected value can be computed by hand.
cost_tablet test_table()
{
  std::istringstream in{
    "register w 0 5 1 50 0\n"
    "plus w 0 10 1 100 0\n"
    "plus_c w 0 4 1 40 0\n"
    "mult w2 0 1 1 300 0\n"
    "bitand w 0 1 1 20 0\n"
    "bitor w 0 1 1 20 0\n"
    "lshr wlogw 0 2 logw 0 30\n"};
  return cost_tablet::from_stream(in, "test");
}

const unsignedbv_typet u32{32};

/// A design built from wire definitions, next-state functions, inputs and
/// outputs.
struct designt
{
  symbol_tablet symbol_table;
  std::vector<exprt> invar, trans;
  std::vector<symbol_exprt> state_vars, outputs;

  symbol_exprt input(const irep_idt &name, const typet &type = u32)
  {
    symbolt symbol{name, type, ID_Verilog};
    symbol.is_input = true;
    symbol_table.add(symbol);
    return symbol.symbol_expr();
  }

  symbol_exprt wire(const irep_idt &name, exprt value)
  {
    symbol_exprt w{name, value.type()};
    invar.push_back(equal_exprt{w, std::move(value)});
    return w;
  }

  symbol_exprt reg(const irep_idt &name, const typet &type = u32)
  {
    symbol_exprt r{name, type};
    state_vars.push_back(r);
    return r;
  }

  void next(const symbol_exprt &r, exprt value)
  {
    exprt next_symbol{ID_next_symbol, r.type()};
    next_symbol.set(ID_identifier, r.get_identifier());
    trans.push_back(equal_exprt{std::move(next_symbol), std::move(value)});
  }

  void output(const irep_idt &name, exprt value)
  {
    outputs.push_back(wire(name, std::move(value)));
  }

  estimation_resultt estimate()
  {
    transt t{
      ID_trans, conjunction(invar), true_exprt{}, conjunction(trans), typet{}};
    namespacet ns{symbol_table};
    null_message_handlert message_handler;
    return ::estimate(
      t,
      state_vars,
      outputs,
      ns,
      test_table(),
      technology_dbt{"45nm"},
      message_handler);
  }
};
} // namespace

SCENARIO("A register fed by an adder")
{
  designt d;
  auto a = d.input("a"), b = d.input("b");
  auto r = d.reg("r");
  d.next(r, plus_exprt{a, b});
  d.output("o", r);
  auto result = d.estimate();

  REQUIRE(result.register_bits == 32);
  REQUIRE(result.register_area_um2 == Approx(5 * 32));
  REQUIRE(result.combinational_area_um2 == Approx(10 * 32));
  REQUIRE(result.operator_count == 1);
  // inputs arrive at 0, the adder takes 100 ps
  REQUIRE(result.critical_path_ps == Approx(100));
}

SCENARIO("Identical logic is costed once")
{
  GIVEN("Two registers with the same next-state function")
  {
    designt d;
    auto a = d.input("a"), b = d.input("b");
    auto r1 = d.reg("r1"), r2 = d.reg("r2");
    d.next(r1, plus_exprt{a, b});
    d.next(r2, plus_exprt{b, a});
    d.output("o1", r1);
    d.output("o2", r2);
    auto result = d.estimate();
    REQUIRE(result.operator_count == 1);
    REQUIRE(result.register_bits == 64);
  }

  GIVEN("Two registers reading one wire")
  {
    designt d;
    auto a = d.input("a"), b = d.input("b");
    auto w = d.wire("w", plus_exprt{a, b});
    auto r1 = d.reg("r1"), r2 = d.reg("r2");
    d.next(r1, w);
    d.next(r2, w);
    d.output("o1", r1);
    d.output("o2", r2);
    REQUIRE(d.estimate().operator_count == 1);
  }
}

SCENARIO("Chains of an associative operator are balanced")
{
  auto chain = [](bool via_wires)
  {
    designt d;
    auto a = d.input("a"), b = d.input("b"), c = d.input("c"), e = d.input("e");
    auto r = d.reg("r");
    if(via_wires)
    {
      auto t1 = d.wire("t1", plus_exprt{a, b});
      auto t2 = d.wire("t2", plus_exprt{t1, c});
      d.next(r, plus_exprt{t2, e});
    }
    else
      d.next(r, plus_exprt{plus_exprt{plus_exprt{a, b}, c}, e});
    d.output("o", r);
    return d.estimate();
  };

  auto direct = chain(false), wires = chain(true);
  REQUIRE(direct.operator_count == 3);
  // two levels of adders, not three
  REQUIRE(direct.critical_path_ps == Approx(200));
  REQUIRE(wires.combinational_area_um2 == direct.combinational_area_um2);
  REQUIRE(wires.critical_path_ps == direct.critical_path_ps);
}

SCENARIO("Only logic that reaches an output is costed")
{
  GIVEN("A register whose value is never observed")
  {
    designt d;
    auto a = d.input("a"), b = d.input("b");
    auto r = d.reg("r");
    d.next(r, mult_exprt{a, b});
    d.output("o", a);
    auto result = d.estimate();
    REQUIRE(result.register_bits == 0);
    REQUIRE(result.combinational_area_um2 == 0);
  }

  GIVEN("Logic between a register and an output")
  {
    designt d;
    auto a = d.input("a"), b = d.input("b");
    auto r = d.reg("r");
    d.next(r, a);
    d.output("o", mult_exprt{r, b});
    auto result = d.estimate();
    REQUIRE(result.combinational_area_um2 == Approx(32 * 32));
    // clock-to-Q of 50 ps, then the multiplier
    REQUIRE(result.critical_path_ps == Approx(350));
  }
}

SCENARIO("Constants")
{
  GIVEN("A bitwise AND with zero")
  {
    designt d;
    auto a = d.input("a");
    d.output("o", bitand_exprt{a, from_integer(0, u32)});
    REQUIRE(d.estimate().combinational_area_um2 == 0);
  }

  GIVEN("A shift by a constant")
  {
    designt d;
    auto a = d.input("a");
    d.output("o", lshr_exprt{a, from_integer(3, u32)});
    REQUIRE(d.estimate().combinational_area_um2 == 0);
  }

  GIVEN("A constant that reaches an adder through a register")
  {
    designt d;
    auto a = d.input("a");
    auto r = d.reg("r");
    d.next(r, from_integer(1, u32));
    d.output("o", plus_exprt{a, r});
    auto result = d.estimate();
    REQUIRE(result.register_bits == 0);
    REQUIRE(result.combinational_area_um2 == Approx(4 * 32));
  }
}

SCENARIO("Values without a hardware width are an error")
{
  designt d;
  floatbv_typet f;
  f.set_width(64);
  f.set_f(52);
  auto a = d.input("a", f);
  d.output("o", a);
  REQUIRE_THROWS_AS(d.estimate(), ebmc_errort);
}
