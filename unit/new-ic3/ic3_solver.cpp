/*******************************************************************\

Module: IC3 Solver Unit Tests

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/std_types.h>

#include <new-ic3/ic3_solver.h>
#include <testing-utils/use_catch.h>

/// Helper: build a netlist with a single 1-bit latch. The latch's
/// current-state is AIG node 0, next-state is `next_lit`. The
/// property literal is `prop_lit`. Initial state is constrained to
/// `init_lit` (a literal over the latch's current-state node).
static netlistt make_single_latch_netlist(
  literalt next_lit,
  literalt init_lit,
  literalt prop_lit)
{
  netlistt netlist;

  // Node 0: primary input (represents the current-state bit)
  literalt current = netlist.new_input();
  REQUIRE(current.var_no() == 0);

  // Register the latch in the var_map.
  var_mapt::vart var;
  var.vartype = var_mapt::vart::vartypet::LATCH;
  var.type = typet(ID_bool);
  var.bits.resize(1);
  var.bits[0].current = current;
  var.bits[0].next = next_lit;
  netlist.var_map.map.emplace("latch0", var);
  netlist.var_map.add("latch0", 0, var);

  // Initial state constraint
  netlist.initial.push_back(init_lit);

  return netlist;
}

SCENARIO("ic3_solvert proves a trivially safe property")
{
  GIVEN("A 1-bit latch initialized to 0 with next=current, property = !latch")
  {
    // Latch: current = node 0, next = node 0 (stays the same)
    // Init: latch = 0 (i.e., !current)
    // Property: !latch (i.e., !current) — always true since latch stays 0
    literalt current{0, false};
    literalt prop_lit = !current; // property is !latch, always true

    auto netlist = make_single_latch_netlist(current, !current, prop_lit);

    null_message_handlert mh;
    ic3_solvert solver(std::move(netlist), prop_lit, mh);

    THEN("IC3 proves the property")
    {
      REQUIRE(solver.solve().outcome == ic3_resultt::outcomet::PROVED);
    }
  }
}

SCENARIO("ic3_solvert refutes a property violated in the initial state")
{
  GIVEN("A 1-bit latch initialized to 1, property = !latch")
  {
    // Latch: current = node 0, next = node 0 (stays the same)
    // Init: latch = 1 (i.e., current is positive)
    // Property: !latch — violated immediately
    literalt current{0, false};
    literalt prop_lit = !current;

    auto netlist = make_single_latch_netlist(current, current, current);

    null_message_handlert mh;
    ic3_solvert solver(std::move(netlist), prop_lit, mh);

    THEN("IC3 refutes the property with a single-state counterexample")
    {
      auto result = solver.solve();
      REQUIRE(result.outcome == ic3_resultt::outcomet::REFUTED);
      REQUIRE(result.counterexample_length == 1);
    }
  }
}

SCENARIO("ic3_solvert refutes a property violated after one step")
{
  GIVEN("A 1-bit latch initialized to 0, next=1, property = !latch")
  {
    // Latch: current = node 0, next = const_literal(true) (flips to 1)
    // Init: latch = 0
    // Property: !latch — holds initially but violated at step 1
    literalt current{0, false};
    literalt prop_lit = !current;

    auto netlist =
      make_single_latch_netlist(const_literal(true), !current, prop_lit);

    null_message_handlert mh;
    ic3_solvert solver(std::move(netlist), prop_lit, mh);

    THEN("IC3 refutes the property with a two-state counterexample")
    {
      auto result = solver.solve();
      REQUIRE(result.outcome == ic3_resultt::outcomet::REFUTED);
      REQUIRE(result.counterexample_length == 2);
    }
  }
}

SCENARIO("ic3_solvert proves a property on a two-latch system")
{
  GIVEN("Two latches: a toggles, b stays 0; property = !b")
  {
    netlistt netlist;

    // Node 0: latch a (toggles)
    literalt a_current = netlist.new_input();
    // Node 1: latch b (stays 0)
    literalt b_current = netlist.new_input();

    // a's next = !a (toggle)
    literalt a_next = !a_current;
    // b's next = b (stays the same)
    literalt b_next = b_current;

    // Register latch a
    var_mapt::vart var_a;
    var_a.vartype = var_mapt::vart::vartypet::LATCH;
    var_a.type = typet(ID_bool);
    var_a.bits.resize(1);
    var_a.bits[0].current = a_current;
    var_a.bits[0].next = a_next;
    netlist.var_map.map.emplace("a", var_a);
    netlist.var_map.add("a", 0, var_a);

    // Register latch b
    var_mapt::vart var_b;
    var_b.vartype = var_mapt::vart::vartypet::LATCH;
    var_b.type = typet(ID_bool);
    var_b.bits.resize(1);
    var_b.bits[0].current = b_current;
    var_b.bits[0].next = b_next;
    netlist.var_map.map.emplace("b", var_b);
    netlist.var_map.add("b", 0, var_b);

    // Init: a=0, b=0
    netlist.initial.push_back(!a_current);
    netlist.initial.push_back(!b_current);

    // Property: !b (always true since b stays 0)
    literalt prop_lit = !b_current;

    null_message_handlert mh;
    ic3_solvert solver(std::move(netlist), prop_lit, mh);

    THEN("IC3 proves the property")
    {
      REQUIRE(solver.solve().outcome == ic3_resultt::outcomet::PROVED);
    }
  }
}

SCENARIO("ic3_solvert proves a property requiring inductive strengthening")
{
  GIVEN("A 2-bit counter that stays in {0,1,2}, property = counter != 3")
  {
    netlistt netlist;

    // Node 0: bit 0 of counter
    literalt b0 = netlist.new_input();
    // Node 1: bit 1 of counter
    literalt b1 = netlist.new_input();
    // Node 2: input (nondeterministic choice to increment or not)
    literalt inp = netlist.new_input();

    // Counter increments when inp=1, saturates at 2.
    // next_b0 = b0 XOR (inp AND !b1)
    //         = b0 XOR (inp AND !b1)
    // next_b1 = b1 XOR (b0 AND inp AND !b1)
    //
    // Simpler encoding: use AND gates in the AIG.
    // !b1
    literalt not_b1 = !b1;

    // inp AND !b1 (only increment if counter < 2, i.e. b1=0)
    literalt inc = netlist.new_and_node(inp, not_b1);

    // b0 XOR inc = (b0 AND !inc) OR (!b0 AND inc)
    //            = !( !(b0 AND !inc) AND !(!b0 AND inc) )
    //            -- build with AND nodes
    literalt b0_and_not_inc = netlist.new_and_node(b0, !inc);
    literalt not_b0_and_inc = netlist.new_and_node(!b0, inc);
    // XOR = !(!a AND !b) when a,b are the two AND terms... no.
    // XOR(a,b) = (a OR b) AND !(a AND b)
    // OR(a,b) = !(!a AND !b)
    literalt or_node = !netlist.new_and_node(!b0_and_not_inc, !not_b0_and_inc);
    // a AND b cannot both be true (they share b0/!b0), so XOR = OR here
    literalt next_b0 = or_node;

    // b0 AND inc (carry into bit 1)
    literalt carry = netlist.new_and_node(b0, inc);

    // b1 XOR carry
    literalt b1_and_not_carry = netlist.new_and_node(b1, !carry);
    literalt not_b1_and_carry = netlist.new_and_node(!b1, carry);
    literalt next_b1 =
      !netlist.new_and_node(!b1_and_not_carry, !not_b1_and_carry);

    // Register latches
    var_mapt::vart var_b0;
    var_b0.vartype = var_mapt::vart::vartypet::LATCH;
    var_b0.type = typet(ID_bool);
    var_b0.bits.resize(1);
    var_b0.bits[0].current = b0;
    var_b0.bits[0].next = next_b0;
    netlist.var_map.map.emplace("b0", var_b0);
    netlist.var_map.add("b0", 0, var_b0);

    var_mapt::vart var_b1;
    var_b1.vartype = var_mapt::vart::vartypet::LATCH;
    var_b1.type = typet(ID_bool);
    var_b1.bits.resize(1);
    var_b1.bits[0].current = b1;
    var_b1.bits[0].next = next_b1;
    netlist.var_map.map.emplace("b1", var_b1);
    netlist.var_map.add("b1", 0, var_b1);

    // Register input
    var_mapt::vart var_inp;
    var_inp.vartype = var_mapt::vart::vartypet::INPUT;
    var_inp.type = typet(ID_bool);
    var_inp.bits.resize(1);
    var_inp.bits[0].current = inp;
    var_inp.bits[0].next = inp;
    netlist.var_map.map.emplace("inp", var_inp);
    netlist.var_map.add("inp", 0, var_inp);

    // Init: counter = 0
    netlist.initial.push_back(!b0);
    netlist.initial.push_back(!b1);

    // Property: counter != 3, i.e., !(b0 AND b1) = !b0 OR !b1 = NAND
    literalt prop_lit = !netlist.new_and_node(b0, b1);

    null_message_handlert mh;
    ic3_solvert solver(std::move(netlist), prop_lit, mh);

    THEN("IC3 proves the property (requires inductive strengthening)")
    {
      REQUIRE(solver.solve().outcome == ic3_resultt::outcomet::PROVED);
    }
  }
}

SCENARIO("ic3_solvert reports the length of a deeper counterexample")
{
  GIVEN("A 2-bit counter that increments every cycle, property = counter != 3")
  {
    netlistt netlist;

    // Node 0: bit 0 of counter
    literalt b0 = netlist.new_input();
    // Node 1: bit 1 of counter
    literalt b1 = netlist.new_input();

    // The counter increments unconditionally:
    // next_b0 = !b0
    literalt next_b0 = !b0;

    // next_b1 = b1 XOR b0, built with AND nodes
    literalt b1_and_not_b0 = netlist.new_and_node(b1, !b0);
    literalt not_b1_and_b0 = netlist.new_and_node(!b1, b0);
    literalt next_b1 = !netlist.new_and_node(!b1_and_not_b0, !not_b1_and_b0);

    // Register latches
    var_mapt::vart var_b0;
    var_b0.vartype = var_mapt::vart::vartypet::LATCH;
    var_b0.type = bool_typet{};
    var_b0.bits.resize(1);
    var_b0.bits[0].current = b0;
    var_b0.bits[0].next = next_b0;
    netlist.var_map.map.emplace("b0", var_b0);
    netlist.var_map.add("b0", 0, var_b0);

    var_mapt::vart var_b1;
    var_b1.vartype = var_mapt::vart::vartypet::LATCH;
    var_b1.type = bool_typet{};
    var_b1.bits.resize(1);
    var_b1.bits[0].current = b1;
    var_b1.bits[0].next = next_b1;
    netlist.var_map.map.emplace("b1", var_b1);
    netlist.var_map.add("b1", 0, var_b1);

    // Init: counter = 0
    netlist.initial.push_back(!b0);
    netlist.initial.push_back(!b1);

    // Property: counter != 3, i.e., !(b0 AND b1)
    literalt prop_lit = !netlist.new_and_node(b0, b1);

    null_message_handlert mh;
    ic3_solvert solver(std::move(netlist), prop_lit, mh);

    THEN("IC3 refutes the property with a four-state counterexample")
    {
      // The system is deterministic with a unique initial state, so
      // the only counterexample is 0, 1, 2, 3: four states.
      auto result = solver.solve();
      REQUIRE(result.outcome == ic3_resultt::outcomet::REFUTED);
      REQUIRE(result.counterexample_length == 4);
    }
  }
}
