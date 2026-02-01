/*******************************************************************\

Module: AIG Nondet Elimination Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <trans-netlist/aig_nondet_elimination.h>

SCENARIO("aig_nondet_elimination with no equivalences")
{
  GIVEN("An AIG with two inputs and an AND node")
  {
    aigt aig;
    auto lit0 = aig.new_input();
    auto lit1 = aig.new_input();
    (void)aig.new_and_node(lit0, lit1);

    aig_plus_constraintst::equivalencest equivalences;

    THEN("the result preserves the structure")
    {
      auto [new_aig, map] = aig_nondet_elimination(aig, equivalences);

      REQUIRE(new_aig.number_of_nodes() == 3);
      REQUIRE(new_aig.nodes[0].is_input());
      REQUIRE(new_aig.nodes[1].is_input());
      REQUIRE(new_aig.nodes[2].is_and());
      new_aig.check_ordering();
    }
  }
}

SCENARIO("aig_nondet_elimination with nondet equivalent to another input")
{
  GIVEN("An AIG with three inputs and an AND, where one input equals another")
  {
    // nodes: in0, in1, in2, AND3(in0, in1)
    aigt aig;
    auto lit0 = aig.new_input();
    auto lit1 = aig.new_input();
    auto lit2 = aig.new_input();
    (void)aig.new_and_node(lit0, lit1);

    // in1 == in2
    aig_plus_constraintst::equivalencest equivalences = {{lit1, lit2}};

    THEN("one input is eliminated")
    {
      auto [new_aig, map] = aig_nondet_elimination(aig, equivalences);

      REQUIRE(new_aig.number_of_nodes() == 3);
      new_aig.check_ordering();

      // Old nodes 1 and 2 map to the same new literal
      REQUIRE(map[1] == map[2]);
    }
  }
}

SCENARIO("aig_nondet_elimination with nondet equivalent to AND node")
{
  GIVEN("An AIG where a nondet input equals an AND node")
  {
    // nodes: in0, in1, in2(nondet), AND3(in0, in1), AND4(in2, AND3)
    aigt aig;
    auto lit0 = aig.new_input();
    auto lit1 = aig.new_input();
    auto lit2 = aig.new_input();
    auto lit3 = aig.new_and_node(lit0, lit1);
    (void)aig.new_and_node(lit2, lit3);

    // in2 == AND3
    aig_plus_constraintst::equivalencest equivalences = {{lit2, lit3}};

    THEN("the nondet input is eliminated")
    {
      auto [new_aig, map] = aig_nondet_elimination(aig, equivalences);

      // in0, in1 survive; in2 eliminated; AND3 and AND4 remain
      REQUIRE(new_aig.number_of_nodes() == 4);
      new_aig.check_ordering();

      // Old node 2 maps to same literal as old node 3
      REQUIRE(map[2] == map[3]);
    }
  }
}

SCENARIO("aig_nondet_elimination with two nondets equivalent")
{
  GIVEN("An AIG where two nondet inputs are equivalent")
  {
    // nodes: in0, in1, AND2(in0, in1)
    aigt aig;
    auto lit0 = aig.new_input();
    auto lit1 = aig.new_input();
    (void)aig.new_and_node(lit0, lit1);

    // in0 == in1
    aig_plus_constraintst::equivalencest equivalences = {{lit0, lit1}};

    THEN("one nondet is eliminated")
    {
      auto [new_aig, map] = aig_nondet_elimination(aig, equivalences);

      REQUIRE(new_aig.number_of_nodes() == 2);
      new_aig.check_ordering();

      // Both old inputs map to the same new literal
      REQUIRE(map(lit0) == map(lit1));
    }
  }
}

SCENARIO("aig_nondet_elimination with negated equivalence")
{
  GIVEN("An AIG where a nondet input equals the negation of another")
  {
    // nodes: in0, in1, AND2(in0, in1)
    aigt aig;
    auto lit0 = aig.new_input();
    auto lit1 = aig.new_input();
    (void)aig.new_and_node(lit0, lit1);

    // !in0 == in1, i.e., in0 == !in1
    aig_plus_constraintst::equivalencest equivalences = {{!lit0, lit1}};

    THEN("the first input is eliminated with negation")
    {
      auto [new_aig, map] = aig_nondet_elimination(aig, equivalences);

      REQUIRE(new_aig.number_of_nodes() == 2);
      new_aig.check_ordering();

      // Old node 0 maps to the negation of old node 1
      REQUIRE(map(lit0) == map(!lit1));
    }
  }
}

SCENARIO("aig_nondet_elimination with equivalence chain")
{
  GIVEN("An AIG with a chain of equivalences between inputs")
  {
    // nodes: in0, in1, in2, AND3(in0, in1)
    aigt aig;
    auto lit0 = aig.new_input();
    auto lit1 = aig.new_input();
    auto lit2 = aig.new_input();
    (void)aig.new_and_node(lit0, lit1);

    // in0 == in1, in1 == in2
    aig_plus_constraintst::equivalencest equivalences = {
      {lit0, lit1}, {lit1, lit2}};

    THEN("the chain is resolved and only one input survives")
    {
      auto [new_aig, map] = aig_nondet_elimination(aig, equivalences);

      new_aig.check_ordering();

      // All three old inputs map to the same literal
      REQUIRE(map(lit0) == map(lit1));
      REQUIRE(map(lit1) == map(lit2));
    }
  }
}

SCENARIO("aig_nondet_elimination ignores equivalence between AND nodes")
{
  GIVEN("An AIG with an equivalence between two AND nodes")
  {
    // nodes: in0, in1, in2, AND3(in0, in1), AND4(in0, in2)
    aigt aig;
    auto lit0 = aig.new_input();
    auto lit1 = aig.new_input();
    auto lit2 = aig.new_input();
    auto lit3 = aig.new_and_node(lit0, lit1);
    auto lit4 = aig.new_and_node(lit0, lit2);

    // AND3 == AND4 (neither is an input)
    aig_plus_constraintst::equivalencest equivalences = {{lit3, lit4}};

    THEN("no nodes are eliminated")
    {
      auto [new_aig, map] = aig_nondet_elimination(aig, equivalences);

      REQUIRE(new_aig.number_of_nodes() == 5);
      new_aig.check_ordering();
    }
  }
}
