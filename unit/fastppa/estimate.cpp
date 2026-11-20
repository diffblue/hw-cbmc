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
#include <testing-utils/use_catch.h>

#include <sstream>

namespace
{
/// Costs chosen so that every expected value can be computed by hand.
cost_tablet test_table()
{
  std::istringstream in{
    "register w 0 5 1 50 0 0 2 0 0.1\n"
    "clock w 0 0 1 0 0 0 3 0 0\n"
    "plus w 0 10 1 100 0 0 4 0 0.2\n"
    "plus_c w 0 4 1 40 0 0 1 0 0.1\n"
    "mult w2 0 1 1 300 0 0 1 0 0.01\n"
    "bitand w 0 1 1 20 0 0 1 0 0.01\n"
    "bitor w 0 1 1 20 0 0 1 0 0.01\n"
    "lshr wlogw 0 2 logw 0 30 0 1 0 0.01\n"};
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
      t, state_vars, outputs, ns, test_table(), message_handler);
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
  // switching energy of the adder and the register, clock energy of the
  // register, leakage of both
  REQUIRE(result.data_energy_fj == Approx(4 * 32 + 2 * 32));
  REQUIRE(result.clock_energy_fj == Approx(3 * 32));
  REQUIRE(result.leakage_uw == Approx(0.2 * 32 + 0.1 * 32));
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

SCENARIO("Built-in cost tables")
{
  const std::vector<std::string> kinds = {
    "register",      "clock", "plus",   "minus",         "plus_c",
    "unary_minus",   "mult",  "mult_c", "div",           "mod",
    "bitand",        "bitor", "bitxor", "bitnot",        "equal",
    "equal_c",       "lt",    "lt_c",   "reduction_and", "reduction_or",
    "reduction_xor", "shl",   "lshr",   "ashr",          "if",
    "index",         "with"};

  for(auto &[name, description] : cost_tablet::process_names())
  {
    auto table = cost_tablet::builtin(name);
    for(auto &kind : kinds)
    {
      const auto &f = table(kind);
      REQUIRE(f.area(32, 16) >= 0);
      REQUIRE(f.delay(32, 16) >= 0);
      REQUIRE(f.energy(32, 16) >= 0);
      REQUIRE(f.leakage(32, 16) >= 0);
    }
    // operators other than the clock cost area
    REQUIRE(table("plus").area(32) > 0);
    REQUIRE(table("plus").delay(32) > 0);
  }

  REQUIRE_THROWS_AS(cost_tablet::builtin("4nm"), ebmc_errort);

  THEN("Smaller nodes have smaller cells")
  {
    // The measured 2nm library (GT2N) is not denser than the 3nm table
    // derived from ASAP7, so it is not part of this sequence.
    const std::vector<std::string> nodes = {
      "180nm",
      "130nm",
      "90nm",
      "65nm",
      "45nm",
      "28nm",
      "14nm",
      "7nm",
      "5nm",
      "3nm"};
    for(std::size_t i = 1; i < nodes.size(); ++i)
    {
      INFO(nodes[i - 1] << " vs " << nodes[i]);
      REQUIRE(
        cost_tablet::builtin(nodes[i])("register").area(1) <
        cost_tablet::builtin(nodes[i - 1])("register").area(1));
    }
  }
}

SCENARIO("Malformed cost tables are rejected")
{
  std::istringstream short_line{"plus w 0 1 1 1 0\n"};
  REQUIRE_THROWS_AS(cost_tablet::from_stream(short_line, "test"), ebmc_errort);
  std::istringstream bad_form{"plus x 0 1 1 1 0 0 0 0 0\n"};
  REQUIRE_THROWS_AS(cost_tablet::from_stream(bad_form, "test"), ebmc_errort);
}
