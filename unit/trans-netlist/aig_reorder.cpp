/*******************************************************************\

Module: AIG Reorder Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <trans-netlist/aig_reorder.h>

static aig_substitution_mapt make_subst(std::initializer_list<literalt> entries)
{
  aig_substitution_mapt map(entries.size());
  literalt::var_not i = 0;
  for(auto lit : entries)
    map[i++] = lit;
  return map;
}

SCENARIO("aig_reorder with identity substitution")
{
  GIVEN("An AIG with two inputs and an AND node")
  {
    aigt aig;
    auto lit0 = aig.new_input();
    auto lit1 = aig.new_input();
    (void)aig.new_and_node(lit0, lit1);

    auto subst =
      make_subst({literalt(0, false), literalt(1, false), literalt(2, false)});

    THEN("the result preserves the structure")
    {
      auto [new_aig, map] = aig_reorder(aig, subst);

      REQUIRE(new_aig.number_of_nodes() == 3);
      REQUIRE(new_aig.nodes[0].is_input());
      REQUIRE(new_aig.nodes[1].is_input());
      REQUIRE(new_aig.nodes[2].is_and());
      new_aig.check_ordering();

      REQUIRE(map[0] == literalt(0, false));
      REQUIRE(map[1] == literalt(1, false));
      REQUIRE(map[2] == literalt(2, false));
    }
  }
}

SCENARIO("aig_reorder eliminating an input")
{
  GIVEN("An AIG where one input is substituted by another")
  {
    // nodes: in0, in1, in2, AND3(in0, in1)
    aigt aig;
    auto lit0 = aig.new_input();
    auto lit1 = aig.new_input();
    (void)aig.new_input();
    (void)aig.new_and_node(lit0, lit1);

    // Substitute node 1 with node 2 (eliminate node 1)
    auto subst = make_subst(
      {literalt(0, false),
       literalt(2, false),
       literalt(2, false),
       literalt(3, false)});

    THEN("the eliminated input is removed and references updated")
    {
      auto [new_aig, map] = aig_reorder(aig, subst);

      REQUIRE(new_aig.number_of_nodes() == 3);
      REQUIRE(new_aig.nodes[0].is_input());
      REQUIRE(new_aig.nodes[1].is_input());
      REQUIRE(new_aig.nodes[2].is_and());
      new_aig.check_ordering();

      // Old nodes 1 and 2 both map to the same new node
      REQUIRE(map[1] == map[2]);
      // AND node references the new nodes
      REQUIRE(new_aig.nodes[2].a == map[0]);
      REQUIRE(new_aig.nodes[2].b == map[1]);
    }
  }
}

SCENARIO("aig_reorder with reordering needed")
{
  GIVEN("An AIG where an input is substituted by a higher-indexed AND node")
  {
    // nodes: in0, in1, in2, AND3(in1, in2), AND4(in0, AND3)
    aigt aig;
    auto lit0 = aig.new_input();
    auto lit1 = aig.new_input();
    auto lit2 = aig.new_input();
    auto lit3 = aig.new_and_node(lit1, lit2);
    (void)aig.new_and_node(lit0, lit3);

    // Substitute node 0 with node 3 (which has higher index)
    auto subst = make_subst(
      {literalt(3, false),
       literalt(1, false),
       literalt(2, false),
       literalt(3, false),
       literalt(4, false)});

    THEN("the result is correctly reordered")
    {
      auto [new_aig, map] = aig_reorder(aig, subst);

      // Node 0 was eliminated, 4 remaining nodes become
      // in(was 1), in(was 2), AND(was 3), AND(was 4)
      REQUIRE(new_aig.number_of_nodes() == 4);
      new_aig.check_ordering();

      // Old node 0 maps to same as old node 3
      REQUIRE(map[0] == map[3]);
    }
  }
}

SCENARIO("aig_reorder translates labels")
{
  GIVEN("An AIG with labeled nodes and identity substitution")
  {
    aigt aig;
    auto lit0 = aig.new_input("a");
    auto lit1 = aig.new_input("b");
    auto lit2 = aig.new_and_node(lit0, lit1); // NOLINT
    aig.label(lit2, "c");

    auto subst =
      make_subst({literalt(0, false), literalt(1, false), literalt(2, false)});

    THEN("labels are preserved in the new AIG")
    {
      auto [new_aig, map] = aig_reorder(aig, subst);

      REQUIRE(new_aig.labeling.count("a"));
      REQUIRE(new_aig.labeling.count("b"));
      REQUIRE(new_aig.labeling.count("c"));
      REQUIRE(new_aig.labeling.at("a") == map[0]);
      REQUIRE(new_aig.labeling.at("b") == map[1]);
      REQUIRE(new_aig.labeling.at("c") == map[2]);
    }
  }

  GIVEN("An AIG with a labeled node that gets eliminated")
  {
    // nodes: in0("a"), in1("b"), AND2(in0, in1)
    aigt aig;
    auto lit0 = aig.new_input("a");
    auto lit1 = aig.new_input("b");
    (void)aig.new_and_node(lit0, lit1);

    // Substitute node 1 with node 0
    auto subst =
      make_subst({literalt(0, false), literalt(0, false), literalt(2, false)});

    THEN("the label of the eliminated node points to the replacement")
    {
      auto [new_aig, map] = aig_reorder(aig, subst);

      REQUIRE(new_aig.labeling.at("a") == map[0]);
      REQUIRE(new_aig.labeling.at("b") == map[1]);
      // Both labels now point to the same node
      REQUIRE(map[0] == map[1]);
    }
  }
}

SCENARIO("aig_reorder with negated substitution")
{
  GIVEN("An AIG where an input is substituted by the negation of another")
  {
    // nodes: in0, in1, AND2(in0, in1)
    aigt aig;
    auto lit0 = aig.new_input();
    auto lit1 = aig.new_input();
    (void)aig.new_and_node(lit0, lit1);

    // Substitute node 1 with !node 0
    auto subst =
      make_subst({literalt(0, false), literalt(0, true), literalt(2, false)});

    THEN("the AND node uses the negated reference")
    {
      auto [new_aig, map] = aig_reorder(aig, subst);

      REQUIRE(new_aig.number_of_nodes() == 2);
      REQUIRE(new_aig.nodes[0].is_input());
      REQUIRE(new_aig.nodes[1].is_and());
      new_aig.check_ordering();

      // Old node 1 maps to negation of old node 0's mapping
      REQUIRE(map[1] == !map[0]);
      // AND node's second input is negated
      REQUIRE(new_aig.nodes[1].b == !new_aig.nodes[1].a);
    }
  }
}
