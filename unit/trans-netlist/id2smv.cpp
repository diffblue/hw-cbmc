/*******************************************************************\

Module: id2smv Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <trans-netlist/smv_netlist.h>

SCENARIO("id2smv")
{
  GIVEN("A plain identifier")
  {
    REQUIRE(id2smv("abc") == "abc");
  }

  GIVEN("An identifier with :: scope separator")
  {
    REQUIRE(id2smv("module::signal") == "module.signal");
  }

  GIVEN("An identifier with a dot")
  {
    REQUIRE(id2smv("a.b") == "a.b");
  }

  GIVEN("An identifier with a special character")
  {
    REQUIRE(id2smv("a@b") == "a$64$b");
  }

  GIVEN("An identifier that is an SMV keyword")
  {
    REQUIRE(id2smv("next") == "\\next");
  }

  GIVEN("A dotted identifier with a keyword component")
  {
    REQUIRE(id2smv("a.next") == "a.\\next");
  }
}
