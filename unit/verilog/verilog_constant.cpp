/*******************************************************************\

Module: is_verilog_constant Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/mathematical_types.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <testing-utils/use_catch.h>
#include <verilog/verilog_constant.h>

SCENARIO("is_verilog_constant")
{
  const unsignedbv_typet u8{8};
  const auto c1 = from_integer(1, u8);
  const auto c2 = from_integer(2, u8);
  const symbol_exprt x{"x", u8};

  GIVEN("a constant")
  {
    REQUIRE(is_verilog_constant(c1));
  }

  GIVEN("$")
  {
    REQUIRE(is_verilog_constant(exprt{ID_infinity, integer_typet{}}));
  }

  GIVEN("a symbol")
  {
    // parameters are expected to have been replaced by their values
    REQUIRE(!is_verilog_constant(x));
  }

  GIVEN("an operator applied to constants")
  {
    // no evaluation is performed
    REQUIRE(!is_verilog_constant(plus_exprt{c1, c2}));
  }

  GIVEN("a system function call with constant argument")
  {
    // system functions are not evaluated
    const exprt call{
      ID_function_call,
      u8,
      {symbol_exprt{"$clog2", code_typet{{}, u8}},
       exprt{ID_arguments, typet{}, {c2}}}};
    REQUIRE(!is_verilog_constant(call));
  }

  GIVEN("an array")
  {
    const array_typet array_type{u8, from_integer(2, integer_typet{})};
    REQUIRE(is_verilog_constant(array_exprt{{c1, c2}, array_type}));
    REQUIRE(!is_verilog_constant(array_exprt{{c1, x}, array_type}));
  }

  GIVEN("a struct")
  {
    const struct_typet struct_type{{{"a", u8}, {"b", u8}}};
    REQUIRE(is_verilog_constant(struct_exprt{{c1, c2}, struct_type}));
    REQUIRE(!is_verilog_constant(struct_exprt{{c1, x}, struct_type}));
  }

  GIVEN("a nested struct with an array member")
  {
    const array_typet array_type{u8, from_integer(2, integer_typet{})};
    const struct_typet struct_type{{{"a", array_type}, {"b", u8}}};
    REQUIRE(is_verilog_constant(
      struct_exprt{{array_exprt{{c1, c2}, array_type}, c1}, struct_type}));
    REQUIRE(!is_verilog_constant(
      struct_exprt{{array_exprt{{c1, x}, array_type}, c1}, struct_type}));
  }

  GIVEN("a union")
  {
    const union_typet union_type{{{"a", u8}}};
    REQUIRE(is_verilog_constant(union_exprt{"a", c1, union_type}));
    REQUIRE(!is_verilog_constant(union_exprt{"a", x, union_type}));
  }
}
