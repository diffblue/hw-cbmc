/*******************************************************************\

Module: $typename Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <verilog/typename.h>
#include <verilog/verilog_types.h>

SCENARIO("$typename(...)")
{
  GIVEN("various Verilog types")
  {
    REQUIRE(verilog_typename(verilog_chandle_typet{}) == "chandle");
    REQUIRE(verilog_typename(verilog_real_typet{}) == "real");
    REQUIRE(
      verilog_typename(verilog_signedbv_typet{10}) == "logic signed[9:0]");
    REQUIRE(verilog_typename(verilog_shortreal_typet{}) == "shortreal");
  }
}
