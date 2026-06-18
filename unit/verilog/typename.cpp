/*******************************************************************\

Module: $typename Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <util/namespace.h>
#include <util/symbol_table.h>

#include <testing-utils/use_catch.h>
#include <verilog/typename.h>
#include <verilog/verilog_types.h>

SCENARIO("$typename(...)")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  GIVEN("various Verilog types")
  {
    REQUIRE(verilog_typename(verilog_byte_typet{}, ns) == "byte");
    REQUIRE(verilog_typename(verilog_chandle_typet{}, ns) == "chandle");
    REQUIRE(verilog_typename(verilog_event_typet{}, ns) == "event");
    REQUIRE(verilog_typename(verilog_int_typet{}, ns) == "int");
    REQUIRE(verilog_typename(verilog_integer_typet{}, ns) == "integer");
    REQUIRE(verilog_typename(verilog_longint_typet{}, ns) == "longint");
    REQUIRE(verilog_typename(verilog_real_typet{}, ns) == "real");
    REQUIRE(verilog_typename(verilog_realtime_typet{}, ns) == "realtime");
    REQUIRE(verilog_typename(verilog_shortint_typet{}, ns) == "shortint");
    REQUIRE(verilog_typename(verilog_shortreal_typet{}, ns) == "shortreal");
    REQUIRE(
      verilog_typename(verilog_signedbv_typet{10}, ns) == "logic signed[9:0]");
  }
}
