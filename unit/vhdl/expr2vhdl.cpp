/*******************************************************************\

Module: expr2vhdl Unit Tests

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>

#include <testing-utils/use_catch.h>
#include <vhdl/expr2vhdl.h>

/// a vector type with the VHDL index range as recorded by the
/// VHDL front-end
static unsignedbv_typet
vector_type(std::size_t width, int left, int right, const char *direction)
{
  unsignedbv_typet type{width};
  type.set("#vhdl_left", left);
  type.set("#vhdl_right", right);
  type.set("#vhdl_direction", direction);
  return type;
}

SCENARIO("Generating VHDL expression strings")
{
  GIVEN("A slice of a vector without a known index range")
  {
    const symbol_exprt v{"v", unsignedbv_typet{8}};
    // bits 4 to 7 of v
    auto slice = extractbits_exprt{v, 4, unsignedbv_typet{4}};
    REQUIRE(expr2vhdl(slice) == "v[7:4]");

    const symbol_exprt i{"i", unsignedbv_typet{32}};
    auto symbolic = extractbits_exprt{v, i, unsignedbv_typet{4}};
    REQUIRE(expr2vhdl(symbolic) == "v[i + 3:i]");
  }

  GIVEN("A slice of a vector with a descending index range")
  {
    const symbol_exprt v{"v", vector_type(8, 15, 8, "vhdl_downto")};
    // bits 0 to 3 of v are v(11 downto 8)
    auto slice = extractbits_exprt{v, 0, unsignedbv_typet{4}};
    REQUIRE(expr2vhdl(slice) == "v(11 downto 8)");

    const symbol_exprt i{"i", unsignedbv_typet{32}};
    auto symbolic = extractbits_exprt{v, i, unsignedbv_typet{4}};
    REQUIRE(expr2vhdl(symbolic) == "v(i + 11 downto i + 8)");
  }

  GIVEN("A slice of a vector with an ascending index range")
  {
    const symbol_exprt v{"v", vector_type(8, 0, 7, "to")};
    // bits 0 to 3 of v are v(4 to 7)
    auto slice = extractbits_exprt{v, 0, unsignedbv_typet{4}};
    REQUIRE(expr2vhdl(slice) == "v(4 to 7)");
  }

  GIVEN("A null slice")
  {
    const symbol_exprt v{"v", unsignedbv_typet{8}};
    const symbol_exprt i{"i", unsignedbv_typet{32}};
    auto slice = extractbits_exprt{v, i, unsignedbv_typet{0}};
    REQUIRE(expr2vhdl(slice) == "v(1 to 0)");
  }
}
