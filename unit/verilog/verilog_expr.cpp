/*******************************************************************\

Module: verilog_expr Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <verilog/verilog_expr.h>
#include <verilog/verilog_types.h>

SCENARIO("verilog_based_unsized_literal_exprt::lower()")
{
  GIVEN("'bx — zero-extend to 32 bits (self-determined)")
  {
    verilog_based_unsized_literal_exprt lit{"x", verilog_unsignedbv_typet{32}};
    auto c = lit.lower();
    REQUIRE(c.get_value() == std::string(31, '0') + 'x');
  }

  GIVEN("'sb1 — sign-extend to 32 bits")
  {
    verilog_based_unsized_literal_exprt lit{"1", verilog_signedbv_typet{32}};
    auto c = lit.lower();
    REQUIRE(c.type() == verilog_signedbv_typet{32});
    REQUIRE(c.get_value() == std::string(32, '1'));
  }

  GIVEN("'hx0 at 64 bits — x-extend (context-determined)")
  {
    verilog_based_unsized_literal_exprt lit{
      "xxxx0000", verilog_unsignedbv_typet{64}};
    auto c = lit.lower();
    REQUIRE(c.get_value() == std::string(60, 'x') + "0000");
  }

  GIVEN("'hF0 at 64 bits — zero-extend (MSB is not x/z)")
  {
    verilog_based_unsized_literal_exprt lit{"11110000", unsignedbv_typet{64}};
    auto c = lit.lower();
    REQUIRE(c.type() == unsignedbv_typet{64});
  }
}

SCENARIO("verilog_based_unsized_literal_exprt::with_context()")
{
  GIVEN("with_context only changes the type width")
  {
    verilog_based_unsized_literal_exprt lit{
      "xxxx0000", verilog_unsignedbv_typet{32}};
    auto extended = lit.with_context(64);
    REQUIRE(extended.value() == "xxxx0000");
    REQUIRE(extended.type() == verilog_unsignedbv_typet{64});
  }
}
