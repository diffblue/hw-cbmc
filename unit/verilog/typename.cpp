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
    REQUIRE(verilog_typename(verilog_byte_typet{}) == "byte");
    REQUIRE(verilog_typename(verilog_chandle_typet{}) == "chandle");
    REQUIRE(verilog_typename(verilog_event_typet{}) == "event");
    REQUIRE(verilog_typename(verilog_int_typet{}) == "int");
    REQUIRE(verilog_typename(verilog_integer_typet{}) == "integer");
    REQUIRE(verilog_typename(verilog_longint_typet{}) == "longint");
    REQUIRE(verilog_typename(verilog_real_typet{}) == "real");
    REQUIRE(verilog_typename(verilog_realtime_typet{}) == "realtime");
    REQUIRE(verilog_typename(verilog_shortint_typet{}) == "shortint");
    REQUIRE(verilog_typename(verilog_shortreal_typet{}) == "shortreal");
    REQUIRE(
      verilog_typename(verilog_signedbv_typet{10}) == "logic signed[9:0]");
  }
}
