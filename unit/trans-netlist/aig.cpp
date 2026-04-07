/*******************************************************************\

Module: AIG Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <trans-netlist/aig.h>

#include <sstream>

static std::string print_aig(const aigt &aig)
{
  std::ostringstream oss;
  aig.print(oss);
  return oss.str();
}

static std::string aig_to_dot(const aigt &aig)
{
  std::ostringstream oss;
  aig.output_dot(oss);
  return oss.str();
}

SCENARIO("aigt output without labels")
{
  GIVEN("An AIG with two input nodes")
  {
    aigt aig{aigt::input_node(), aigt::input_node()};

    THEN("print outputs the nodes with numeric identifiers")
    {
      REQUIRE(print_aig(aig) == "n0 = 0\nn1 = 1\n");
    }

    THEN("output_dot outputs the nodes with numeric identifiers")
    {
      REQUIRE(
        aig_to_dot(aig) ==
        "TRUE [label=\"TRUE\", shape=box]\n"
        "0 [label=\"0\",shape=box]\n"
        "1 [label=\"1\",shape=box]\n");
    }
  }

  GIVEN("An AIG with an AND node")
  {
    aigt aig{
      aigt::input_node(),
      aigt::input_node(),
      aigt::and_node({0, false}, {1, false})};

    THEN("print outputs the AND as a conjunction")
    {
      REQUIRE(print_aig(aig) == "n0 = 0\nn1 = 1\nn2 = 0 & 1\n");
    }

    THEN("output_dot outputs the AND node and edges")
    {
      REQUIRE(
        aig_to_dot(aig) ==
        "TRUE [label=\"TRUE\", shape=box]\n"
        "0 [label=\"0\",shape=box]\n"
        "1 [label=\"1\",shape=box]\n"
        "2 [label=\"2\"]\n"
        "0 -> 2\n"
        "1 -> 2\n");
    }
  }

  GIVEN("An AIG with negated inputs to AND")
  {
    aigt aig;
    auto lit0 = aig.new_input();
    auto lit1 = aig.new_input();
    (void)aig.new_and_node(!lit0, lit1);

    THEN("print outputs the negation")
    {
      REQUIRE(print_aig(aig) == "n0 = 0\nn1 = 1\nn2 = !(0) & 1\n");
    }

    THEN("output_dot shows negated edge with odiamond arrowhead")
    {
      REQUIRE(
        aig_to_dot(aig) ==
        "TRUE [label=\"TRUE\", shape=box]\n"
        "0 [label=\"0\",shape=box]\n"
        "1 [label=\"1\",shape=box]\n"
        "2 [label=\"2\"]\n"
        "0 -> 2 [arrowhead=odiamond]\n"
        "1 -> 2\n");
    }
  }
}

SCENARIO("aigt output with labels")
{
  GIVEN("An AIG with labeled input nodes")
  {
    aigt aig;
    (void)aig.new_input("a");
    (void)aig.new_input("b");

    THEN("print outputs the nodes with labels")
    {
      REQUIRE(print_aig(aig) == "n0 = a\nn1 = b\n");
    }

    THEN("output_dot outputs the nodes with labels")
    {
      REQUIRE(
        aig_to_dot(aig) ==
        "TRUE [label=\"TRUE\", shape=box]\n"
        "0 [label=\"a\",shape=box]\n"
        "1 [label=\"b\",shape=box]\n");
    }
  }

  GIVEN("An AIG with labeled AND node")
  {
    aigt aig;
    auto lit0 = aig.new_input();
    auto lit1 = aig.new_input();
    auto lit2 = aig.new_and_node(lit0, lit1);
    aig.label(lit0, "a");
    aig.label(lit1, "b");
    aig.label(lit2, "c");

    THEN("print outputs the AND with labels")
    {
      REQUIRE(print_aig(aig) == "n0 = a\nn1 = b\nn2 = a & b\n");
    }

    THEN("output_dot outputs the AND node with label")
    {
      REQUIRE(
        aig_to_dot(aig) ==
        "TRUE [label=\"TRUE\", shape=box]\n"
        "0 [label=\"a\",shape=box]\n"
        "1 [label=\"b\",shape=box]\n"
        "2 [label=\"c\"]\n"
        "0 -> 2\n"
        "1 -> 2\n");
    }
  }

  GIVEN("An AIG with negated labeled literal")
  {
    aigt aig;
    auto lit0 = aig.new_input("a");
    aig.label(!lit0, "not_a");

    THEN("print outputs the negated label with !")
    {
      REQUIRE(print_aig(aig) == "n0 = a,!not_a\n");
    }

    THEN("output_dot shows the negated label")
    {
      REQUIRE(
        aig_to_dot(aig) ==
        "TRUE [label=\"TRUE\", shape=box]\n"
        "0 [label=\"a,!not_a\",shape=box]\n");
    }
  }

  GIVEN("An AIG with multiple labels on the same node")
  {
    aigt aig;
    auto lit0 = aig.new_input();
    aig.label(lit0, "x");
    aig.label(!lit0, "y");

    THEN("output_dot combines labels with comma")
    {
      auto dot = aig_to_dot(aig);
      REQUIRE(
        dot ==
        "TRUE [label=\"TRUE\", shape=box]\n"
        "0 [label=\"x,!y\",shape=box]\n");
    }
  }
}

SCENARIO("aigt convenience helpers")
{
  GIVEN("input_node factory")
  {
    auto node = aigt::input_node();
    REQUIRE(node.is_var());
    REQUIRE(!node.is_and());
  }

  GIVEN("and_node factory")
  {
    auto node = aigt::and_node({0, false}, {1, false});
    REQUIRE(node.is_and());
    REQUIRE(!node.is_var());
    REQUIRE(node.a == literalt{0, false});
    REQUIRE(node.b == literalt{1, false});
  }

  GIVEN("and_node factory with literals with different polarity")
  {
    auto node = aigt::and_node({0, true}, {1, false});
    REQUIRE(node.is_and());
    REQUIRE(node.a == literalt{0, true});
    REQUIRE(node.b == literalt{1, false});
  }

  GIVEN("initializer list constructor")
  {
    aigt aig{aigt::input_node(), aigt::input_node()};
    REQUIRE(aig.number_of_nodes() == 2);
    REQUIRE(aig.nodes[0].is_var());
    REQUIRE(aig.nodes[1].is_var());
  }

  GIVEN("initializer list constructor with and nodes")
  {
    aigt aig{
      aigt::input_node(),
      aigt::input_node(),
      aigt::and_node({0, false}, {1, false})};
    REQUIRE(aig.number_of_nodes() == 3);
    REQUIRE(aig.nodes[0].is_var());
    REQUIRE(aig.nodes[1].is_var());
    REQUIRE(aig.nodes[2].is_and());
    REQUIRE(aig.nodes[2].a == literalt{0, false});
    REQUIRE(aig.nodes[2].b == literalt{1, false});
  }

  GIVEN("empty initializer list")
  {
    aigt aig{};
    REQUIRE(aig.empty());
  }
}
