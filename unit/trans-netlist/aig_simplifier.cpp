/*******************************************************************\

Module: AIG Simplifier Unit Tests

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <trans-netlist/aig.h>
#include <trans-netlist/aig_simplifier.h>

SCENARIO("AIG simplification with equivalences")
{
  GIVEN("An empty AIG")
  {
    aigt aig;

    THEN("Simplification returns an empty AIG")
    {
      auto [result, _] = aig_simplify(aig, {});
      REQUIRE(result.empty());
    }
  }

  GIVEN("An AIG with inputs and no equivalences")
  {
    aigt aig{aigt::input_node(), aigt::input_node(), aigt::input_node()};

    THEN("Simplification preserves all nodes")
    {
      auto [result, _] = aig_simplify(aig, {});
      REQUIRE(result.number_of_nodes() == 3);
      REQUIRE(result.nodes[0].is_input());
      REQUIRE(result.nodes[1].is_input());
      REQUIRE(result.nodes[2].is_input());
    }
  }

  GIVEN("An AIG with an AND node and no equivalences")
  {
    aigt aig{
      aigt::input_node(),
      aigt::input_node(),
      aigt::and_node({0, false}, {1, false})};

    THEN("Simplification preserves the structure")
    {
      auto [result, _] = aig_simplify(aig, {});
      REQUIRE(result.number_of_nodes() == 3);
      REQUIRE(result.nodes[0].is_input());
      REQUIRE(result.nodes[1].is_input());
      REQUIRE(result.nodes[2].is_and());
      REQUIRE(result.nodes[2].a == literalt{0, false});
      REQUIRE(result.nodes[2].b == literalt{1, false});
    }
  }

  GIVEN("An AIG where two inputs are equivalent")
  {
    aigt aig;
    auto v0 = aig.new_input();      // node 0
    auto v1 = aig.new_input();      // node 1
    (void)aig.new_and_node(v0, v1); // node 2: v0 AND v1

    // v0 is equivalent to v1
    equivalencest equivalences = {{v0, v1}};

    THEN("The AND simplifies to just the variable")
    {
      auto [result, _] = aig_simplify(aig, equivalences);
      // v0 AND v1 becomes v0 AND v0 = v0
      // Only the representative variable node is created
      REQUIRE(result.number_of_nodes() == 1);
      REQUIRE(result.nodes[0].is_input());
    }
  }

  GIVEN("An AIG where a variable is equivalent to the negation of another")
  {
    aigt aig;
    auto v0 = aig.new_input();      // node 0
    auto v1 = aig.new_input();      // node 1
    (void)aig.new_and_node(v0, v1); // node 2: v0 AND v1

    // v0 is equivalent to NOT v1
    equivalencest equivalences = {{v0, !v1}};

    THEN("The AND simplifies to false")
    {
      auto [result, _] = aig_simplify(aig, equivalences);
      // v0 AND v1 becomes v0 AND !v0 = false (constant)
      // Only the representative variable node is created
      REQUIRE(result.number_of_nodes() == 1);
      REQUIRE(result.nodes[0].is_input());
    }
  }

  GIVEN("Transitive equivalences")
  {
    aigt aig;
    auto v0 = aig.new_input();      // node 0
    auto v1 = aig.new_input();      // node 1
    auto v2 = aig.new_input();      // node 2
    (void)aig.new_and_node(v0, v2); // node 3: v0 AND v2

    // v0 ≡ v1 and v1 ≡ v2, so transitively v0 ≡ v2
    equivalencest equivalences = {{v0, v1}, {v1, v2}};

    THEN("The AND simplifies using transitive equivalence")
    {
      auto [result, _] = aig_simplify(aig, equivalences);
      // v0 AND v2 becomes v0 AND v0 = v0
      // Only the representative variable node is created
      REQUIRE(result.number_of_nodes() == 1);
      REQUIRE(result.nodes[0].is_input());
    }
  }

  GIVEN("A chain of AND nodes with equivalences")
  {
    aigt aig;
    auto v0 = aig.new_input();            // node 0
    auto v1 = aig.new_input();            // node 1
    auto v2 = aig.new_input();            // node 2
    auto and1 = aig.new_and_node(v0, v1); // node 3: v0 AND v1
    (void)aig.new_and_node(and1, v2);     // node 4: (v0 AND v1) AND v2

    // v1 ≡ v2
    equivalencest equivalences = {{v1, v2}};

    THEN("The simplification is applied correctly")
    {
      auto [result, _] = aig_simplify(aig, equivalences);
      // (v0 AND v1) AND v2 becomes (v0 AND v1) AND v1
      // v0, v1 are created, then AND(v0, v1), then AND(AND(v0,v1), v1)
      REQUIRE(result.number_of_nodes() == 4);
      REQUIRE(result.nodes[0].is_input());
      REQUIRE(result.nodes[1].is_input());
      // First AND: v0 AND v1
      REQUIRE(result.nodes[2].is_and());
      REQUIRE(result.nodes[2].a == literalt{0, false});
      REQUIRE(result.nodes[2].b == literalt{1, false});
      // Second AND: v1 AND (v0 AND v1)
      REQUIRE(result.nodes[3].is_and());
      REQUIRE(result.nodes[3].a == literalt{1, false});
      REQUIRE(result.nodes[3].b == literalt{2, false});
    }
  }

  GIVEN("An AIG with multiple independent AND nodes")
  {
    aigt aig;
    auto v0 = aig.new_input();      // node 0
    auto v1 = aig.new_input();      // node 1
    auto v2 = aig.new_input();      // node 2
    (void)aig.new_and_node(v0, v1); // node 3: v0 AND v1
    (void)aig.new_and_node(v1, v2); // node 4: v1 AND v2

    THEN("Simplification preserves the structure")
    {
      auto [result, _] = aig_simplify(aig, {});
      REQUIRE(result.number_of_nodes() == 5);
      REQUIRE(result.nodes[0].is_input());
      REQUIRE(result.nodes[1].is_input());
      REQUIRE(result.nodes[2].is_input());
      // First AND: v0 AND v1
      REQUIRE(result.nodes[3].is_and());
      REQUIRE(result.nodes[3].a == literalt{0, false});
      REQUIRE(result.nodes[3].b == literalt{1, false});
      // Second AND: v1 AND v2
      REQUIRE(result.nodes[4].is_and());
      REQUIRE(result.nodes[4].a == literalt{1, false});
      REQUIRE(result.nodes[4].b == literalt{2, false});
    }
  }

  GIVEN("An AIG with negated inputs to AND")
  {
    aigt aig;
    auto v0 = aig.new_input();       // node 0
    auto v1 = aig.new_input();       // node 1
    (void)aig.new_and_node(!v0, v1); // node 2: !v0 AND v1

    THEN("Simplification preserves the negation")
    {
      auto [result, _] = aig_simplify(aig, {});
      REQUIRE(result.number_of_nodes() == 3);
      REQUIRE(result.nodes[0].is_input());
      REQUIRE(result.nodes[1].is_input());
      REQUIRE(result.nodes[2].is_and());
      REQUIRE(result.nodes[2].a == literalt{0, true}); // negated
      REQUIRE(result.nodes[2].b == literalt{1, false});
    }
  }

  GIVEN("An AIG with both inputs negated")
  {
    aigt aig;
    auto v0 = aig.new_var_node();     // node 0
    auto v1 = aig.new_var_node();     // node 1
    (void)aig.new_and_node(!v0, !v1); // node 2: !v0 AND !v1

    equivalencest equivalences;

    THEN("Simplification preserves both negations")
    {
      auto [result, _] = aig_simplify(aig, equivalences);
      REQUIRE(result.number_of_nodes() == 3);
      REQUIRE(result.nodes[0].is_input());
      REQUIRE(result.nodes[1].is_input());
      REQUIRE(result.nodes[2].is_and());
      REQUIRE(result.nodes[2].a == literalt{0, true}); // negated
      REQUIRE(result.nodes[2].b == literalt{1, true}); // negated
    }
  }

  GIVEN("An AIG with double negation equivalence")
  {
    aigt aig;
    auto v0 = aig.new_input();      // node 0
    auto v1 = aig.new_input();      // node 1
    auto v2 = aig.new_input();      // node 2
    (void)aig.new_and_node(v0, v2); // node 3: v0 AND v2

    // v0 ≡ !v1 and v1 ≡ !v2
    // This means v0 ≡ !v1 ≡ !!v2 ≡ v2
    equivalencest equivalences = {{v0, !v1}, {v1, !v2}};

    THEN("The double negation is handled correctly")
    {
      auto [result, _] = aig_simplify(aig, equivalences);
      // v0 AND v2: since v0 ≡ v2, becomes v0 AND v0 = v0
      REQUIRE(result.number_of_nodes() == 1);
      REQUIRE(result.nodes[0].is_input());
    }
  }

  GIVEN("An AIG where equivalence creates a tautology check")
  {
    aigt aig;
    auto v0 = aig.new_input();       // node 0
    auto v1 = aig.new_input();       // node 1
    (void)aig.new_and_node(v0, !v1); // node 2: v0 AND !v1

    // v0 ≡ v1
    equivalencest equivalences = {{v0, v1}};

    THEN("The AND of x and !x becomes false")
    {
      auto [result, _] = aig_simplify(aig, equivalences);
      // v0 AND !v1 becomes v0 AND !v0 = false
      REQUIRE(result.number_of_nodes() == 1);
      REQUIRE(result.nodes[0].is_input());
    }
  }

  GIVEN("A deeper AIG with multiple levels")
  {
    aigt aig;
    auto v0 = aig.new_input();            // node 0
    auto v1 = aig.new_input();            // node 1
    auto v2 = aig.new_input();            // node 2
    auto v3 = aig.new_input();            // node 3
    auto and1 = aig.new_and_node(v0, v1); // node 4: v0 AND v1
    auto and2 = aig.new_and_node(v2, v3); // node 5: v2 AND v3
    (void)aig.new_and_node(and1, and2);   // node 6: (v0 AND v1) AND (v2 AND v3)

    THEN("Simplification preserves the deep structure")
    {
      auto [result, _] = aig_simplify(aig, {});
      REQUIRE(result.number_of_nodes() == 7);
      // Check all variable nodes
      REQUIRE(result.nodes[0].is_input());
      REQUIRE(result.nodes[1].is_input());
      REQUIRE(result.nodes[2].is_input());
      REQUIRE(result.nodes[3].is_input());
      // First AND: v0 AND v1
      REQUIRE(result.nodes[4].is_and());
      REQUIRE(result.nodes[4].a == literalt{0, false});
      REQUIRE(result.nodes[4].b == literalt{1, false});
      // Second AND: v2 AND v3
      REQUIRE(result.nodes[5].is_and());
      REQUIRE(result.nodes[5].a == literalt{2, false});
      REQUIRE(result.nodes[5].b == literalt{3, false});
      // Top AND: (v0 AND v1) AND (v2 AND v3)
      REQUIRE(result.nodes[6].is_and());
      REQUIRE(result.nodes[6].a == literalt{4, false});
      REQUIRE(result.nodes[6].b == literalt{5, false});
    }
  }

  GIVEN("An AIG with negated equivalence applied to AND")
  {
    aigt aig;
    auto v0 = aig.new_input();      // node 0
    auto v1 = aig.new_input();      // node 1
    auto v2 = aig.new_input();      // node 2
    (void)aig.new_and_node(v0, v2); // node 3: v0 AND v2

    // v1 ≡ !v2 means v2 should be replaced with !v1
    equivalencest equivalences = {{v1, !v2}};

    THEN("The negation is correctly propagated")
    {
      auto [result, _] = aig_simplify(aig, equivalences);
      // v0 AND v2 becomes v0 AND !v1
      REQUIRE(result.number_of_nodes() == 3);
      REQUIRE(result.nodes[0].is_input());
      REQUIRE(result.nodes[1].is_input());
      REQUIRE(result.nodes[2].is_and());
      REQUIRE(result.nodes[2].a == literalt{0, false});
      REQUIRE(
        result.nodes[2].b == literalt{1, true}); // negated due to equivalence
    }
  }
}

SCENARIO("AIG simplification preserves and re-numbers labeling")
{
  GIVEN("An AIG with labeled inputs and no equivalences")
  {
    aigt aig;
    auto v0 = aig.new_input("input_a"); // node 0
    auto v1 = aig.new_input("input_b"); // node 1
    (void)aig.new_and_node(v0, v1);     // node 2

    THEN("Simplification preserves the labels")
    {
      auto [result, _] = aig_simplify(aig, {});
      REQUIRE(result.number_of_nodes() == 3);
      REQUIRE(result.labeling.size() == 2);
      REQUIRE(result.labeling.at("input_a") == literalt{0, false});
      REQUIRE(result.labeling.at("input_b") == literalt{1, false});
    }
  }

  GIVEN("An AIG with labeled inputs where one is merged")
  {
    aigt aig;
    auto v0 = aig.new_input("input_a"); // node 0
    auto v1 = aig.new_input("input_b"); // node 1
    auto v2 = aig.new_input("input_c"); // node 2
    (void)aig.new_and_node(v0, v2);     // node 3

    // v1 ≡ v2 means v2 should be replaced with v1
    equivalencest equivalences = {{v1, v2}};

    THEN("Labels are re-numbered to the merged node")
    {
      auto [result, _] = aig_simplify(aig, equivalences);
      // v2 is merged into v1, so only v0 and v1 remain
      REQUIRE(result.number_of_nodes() == 3); // v0, v1, AND node
      REQUIRE(result.labeling.size() == 3);
      REQUIRE(result.labeling.at("input_a") == literalt{0, false});
      REQUIRE(result.labeling.at("input_b") == literalt{1, false});
      // input_c was on v2, which is now equivalent to v1
      REQUIRE(result.labeling.at("input_c") == literalt{1, false});
    }
  }

  GIVEN("An AIG with a labeled input that becomes negated")
  {
    aigt aig;
    auto v0 = aig.new_input("input_a"); // node 0
    auto v1 = aig.new_input("input_b"); // node 1
    aig.label(!v1, "not_input_b");
    (void)aig.new_and_node(v0, v1); // node 2

    THEN("Negated labels are preserved")
    {
      auto [result, _] = aig_simplify(aig, {});
      REQUIRE(result.number_of_nodes() == 3);
      REQUIRE(result.labeling.size() == 3);
      REQUIRE(result.labeling.at("input_a") == literalt{0, false});
      REQUIRE(result.labeling.at("input_b") == literalt{1, false});
      REQUIRE(result.labeling.at("not_input_b") == literalt{1, true});
    }
  }

  GIVEN("An AIG with a labeled input that is equivalent to a negation")
  {
    aigt aig;
    auto v0 = aig.new_input("input_a"); // node 0
    auto v1 = aig.new_input("input_b"); // node 1
    auto v2 = aig.new_input("input_c"); // node 2
    (void)aig.new_and_node(v0, v2);     // node 3

    // v1 ≡ !v2 means v2 should be replaced with !v1
    equivalencest equivalences = {{v1, !v2}};

    THEN("Labels are re-numbered with correct negation")
    {
      auto [result, _] = aig_simplify(aig, equivalences);
      REQUIRE(result.number_of_nodes() == 3); // v0, v1, AND node
      REQUIRE(result.labeling.size() == 3);
      REQUIRE(result.labeling.at("input_a") == literalt{0, false});
      REQUIRE(result.labeling.at("input_b") == literalt{1, false});
      // input_c was on v2, which is equivalent to !v1
      REQUIRE(result.labeling.at("input_c") == literalt{1, true});
    }
  }

  GIVEN("An AIG with a labeled AND node")
  {
    aigt aig;
    auto v0 = aig.new_input("input_a");       // node 0
    auto v1 = aig.new_input("input_b");       // node 1
    auto and_node = aig.new_and_node(v0, v1); // node 2
    aig.label(and_node, "and_output");

    THEN("AND node label is preserved")
    {
      auto [result, _] = aig_simplify(aig, {});
      REQUIRE(result.number_of_nodes() == 3);
      REQUIRE(result.labeling.size() == 3);
      REQUIRE(result.labeling.at("input_a") == literalt{0, false});
      REQUIRE(result.labeling.at("input_b") == literalt{1, false});
      REQUIRE(result.labeling.at("and_output") == literalt{2, false});
    }
  }

  GIVEN("An AIG with a labeled AND node that simplifies to a variable")
  {
    aigt aig;
    auto v0 = aig.new_input("input_a");       // node 0
    auto v1 = aig.new_input("input_b");       // node 1
    auto and_node = aig.new_and_node(v0, v1); // node 2
    aig.label(and_node, "and_output");

    // v0 ≡ v1 means AND(v0, v1) = v0
    equivalencest equivalences = {{v0, v1}};

    THEN("AND node label points to the simplified variable")
    {
      auto [result, _] = aig_simplify(aig, equivalences);
      REQUIRE(result.number_of_nodes() == 1);
      REQUIRE(result.labeling.size() == 3);
      REQUIRE(result.labeling.at("input_a") == literalt{0, false});
      REQUIRE(result.labeling.at("input_b") == literalt{0, false});
      // AND(v0, v0) = v0
      REQUIRE(result.labeling.at("and_output") == literalt{0, false});
    }
  }

  GIVEN("An AIG with a labeled AND node that simplifies to false")
  {
    aigt aig;
    auto v0 = aig.new_input("input_a");       // node 0
    auto v1 = aig.new_input("input_b");       // node 1
    auto and_node = aig.new_and_node(v0, v1); // node 2
    aig.label(and_node, "and_output");

    // v0 ≡ !v1 means AND(v0, v1) = AND(v0, !v0) = false
    equivalencest equivalences = {{v0, !v1}};

    THEN("AND node label points to false")
    {
      auto [result, _] = aig_simplify(aig, equivalences);
      REQUIRE(result.number_of_nodes() == 1);
      REQUIRE(result.labeling.size() == 3);
      REQUIRE(result.labeling.at("input_a") == literalt{0, false});
      REQUIRE(result.labeling.at("input_b") == literalt{0, true});
      // AND(v0, !v0) = false
      REQUIRE(result.labeling.at("and_output") == const_literal(false));
    }
  }
}
