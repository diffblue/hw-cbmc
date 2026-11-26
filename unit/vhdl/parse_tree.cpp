/*******************************************************************\

Module: VHDL Parse Tree Unit Tests

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/std_expr.h>

#include <testing-utils/use_catch.h>
#include <vhdl/vhdl_parse_tree.h>

SCENARIO("VHDL design unit identifiers")
{
  GIVEN("An entity item with a mixed-case name")
  {
    vhdl_parse_treet::itemt item;
    item.set_item_type("entity");
    item.set_name(symbol_exprt{"Counter", typet{}});

    THEN("the pretty name keeps the case, the identifier is lower case")
    {
      REQUIRE(item.is_entity());
      REQUIRE(!item.is_architecture());
      REQUIRE(item.get_pretty_name() == "Counter");
      REQUIRE(item.get_identifier() == "counter");
    }
  }

  GIVEN("An architecture item")
  {
    vhdl_parse_treet::itemt item;
    item.set_item_type("architecture");
    item.set_name(symbol_exprt{"RTL", typet{}});
    item.add(ID_entity) = symbol_exprt{"Counter", typet{}};

    THEN("the entity identifier is lower case")
    {
      REQUIRE(item.is_architecture());
      REQUIRE(item.get_identifier() == "rtl");
      REQUIRE(item.get_entity_identifier() == "counter");
    }
  }

  GIVEN("Identifiers")
  {
    THEN("to_lower is case folding (IEEE 1076-2008 15.4.2)")
    {
      REQUIRE(vhdl_parse_treet::itemt::to_lower("Std_Logic") == "std_logic");
      REQUIRE(vhdl_parse_treet::itemt::to_lower("abc_1") == "abc_1");
    }
  }
}

SCENARIO("VHDL extended identifiers")
{
  GIVEN("Extended identifiers that differ in case")
  {
    THEN("they stay distinct (IEEE 1076-2008 15.4.3)")
    {
      REQUIRE(vhdl_parse_treet::itemt::to_lower("\\Foo\\") == "\\Foo\\");
      REQUIRE(
        vhdl_parse_treet::itemt::to_lower("\\Foo\\") !=
        vhdl_parse_treet::itemt::to_lower("\\foo\\"));
    }
  }
}
