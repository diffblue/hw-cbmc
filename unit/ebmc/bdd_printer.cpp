/*******************************************************************\

Module: Unit Tests for BDD Printer

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <ebmc/bdd_printer.h>
#include <solvers/bdd/miniBDD/miniBDD.h>
#include <testing-utils/use_catch.h>

#include <sstream>

static std::string to_string(const mini_bddt &bdd)
{
  std::ostringstream out;
  print_bdd(bdd, out);
  return out.str();
}

SCENARIO("print_bdd for constant BDDs")
{
  GIVEN("a BDD manager")
  {
    mini_bdd_mgrt mgr;

    THEN("the false BDD prints as 'false'")
    {
      REQUIRE(to_string(mgr.False()) == "false\n");
    }

    THEN("the true BDD prints as 'true'")
    {
      REQUIRE(to_string(mgr.True()) == "true\n");
    }
  }
}

SCENARIO("print_bdd for a single variable")
{
  GIVEN("a BDD manager with one variable 'a'")
  {
    mini_bdd_mgrt mgr;
    const auto a = mgr.Var("a");

    THEN("the variable BDD prints as a single cube")
    {
      REQUIRE(to_string(a) == "a\n");
    }

    THEN("the negated variable BDD prints with negation prefix")
    {
      REQUIRE(to_string(!a) == u8"\u00aca\n");
    }
  }
}

SCENARIO("print_bdd for two variables")
{
  GIVEN("a BDD manager with variables 'a' and 'b'")
  {
    mini_bdd_mgrt mgr;
    const auto a = mgr.Var("a");
    const auto b = mgr.Var("b");

    THEN("conjunction prints as a single cube")
    {
      REQUIRE(to_string(a & b) == u8"a \u2227 b\n");
    }

    THEN("disjunction prints as two cubes")
    {
      // BDD has 'a' at root: low=b, high=true
      // low branch gives ¬a ∧ b, high branch gives a
      REQUIRE(to_string(a | b) == u8"\u00aca \u2227 b\na\n");
    }

    THEN("XOR prints as two cubes")
    {
      // BDD has 'a' at root: low=b, high=!b
      REQUIRE(to_string(a ^ b) == u8"\u00aca \u2227 b\na \u2227 \u00acb\n");
    }
  }
}
