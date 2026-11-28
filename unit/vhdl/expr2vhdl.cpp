/*******************************************************************\

Module: expr2vhdl Unit Tests

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/mathematical_expr.h>
#include <util/std_expr.h>

#include <temporal-logic/ltl.h>
#include <testing-utils/use_catch.h>
#include <vhdl/expr2vhdl.h>
#include <vhdl/vhdl_lowering.h>
#include <vhdl/vhdl_types.h>

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

  GIVEN("The lowered types of the VHDL front-end")
  {
    // the lowering records the VHDL type name and the index range
    auto slv = vhdl_lowering(
      vhdl_vector_type("std_logic_vector", {7, 0, vhdl_directiont::DOWNTO}));
    auto bit = vhdl_lowering(vhdl_bit_type());
    auto integer = vhdl_lowering(vhdl_integer_type());
    const symbol_exprt v{"v", slv};
    const symbol_exprt b{"b", bit};
    const symbol_exprt n{"n", integer};

    THEN("types are printed with their VHDL names")
    {
      REQUIRE(type2vhdl(slv) == "std_logic_vector(7 downto 0)");
      REQUIRE(type2vhdl(bit) == "bit");
      REQUIRE(type2vhdl(integer) == "integer");
      REQUIRE(type2vhdl(unsignedbv_typet{4}) == "bit_vector(3 downto 0)");
    }

    THEN("constants are printed as VHDL literals")
    {
      REQUIRE(expr2vhdl(constant_exprt{ID_true, bit}) == "'1'");
      REQUIRE(expr2vhdl(true_exprt{}) == "true");
      REQUIRE(expr2vhdl(from_integer(5, slv)) == "\"00000101\"");
      REQUIRE(expr2vhdl(from_integer(-3, integer)) == "-3");
      REQUIRE(
        expr2vhdl(
          vhdl_lowering(vhdl_integer_constant(7, vhdl_integer_type()))) == "7");
    }

    THEN("indexed names map bit positions to indices")
    {
      REQUIRE(expr2vhdl(extractbit_exprt{v, 0}) == "v(0)");
      auto to = vhdl_lowering(
        vhdl_vector_type("bit_vector", {0, 7, vhdl_directiont::TO}));
      REQUIRE(expr2vhdl(extractbit_exprt{symbol_exprt{"w", to}, 7}) == "w(0)");
      REQUIRE(
        expr2vhdl(extractbits_exprt{v, 4, unsignedbv_typet{4}}) ==
        "v(7 downto 4)");
    }

    THEN("operators use VHDL syntax and precedence")
    {
      REQUIRE(expr2vhdl(and_exprt{b, not_exprt{b}}) == "b and not b");
      REQUIRE(expr2vhdl(or_exprt{and_exprt{b, b}, b}) == "(b and b) or b");
      REQUIRE(expr2vhdl(equal_exprt{n, from_integer(1, integer)}) == "n = 1");
      REQUIRE(expr2vhdl(notequal_exprt{n, plus_exprt{n, n}}) == "n /= n + n");
      REQUIRE(expr2vhdl(mult_exprt{plus_exprt{n, n}, n}) == "(n + n) * n");
      REQUIRE(expr2vhdl(bitand_exprt{v, bitnot_exprt{v}}) == "v and not v");
      REQUIRE(
        expr2vhdl(concatenation_exprt{b, v, unsignedbv_typet{9}}) == "b & v");
      REQUIRE(
        expr2vhdl(if_exprt{b, n, from_integer(0, integer)}) ==
        "(n when b else 0)");
      REQUIRE(expr2vhdl(G_exprt{implies_exprt{b, b}}) == "always b -> b");
      REQUIRE(expr2vhdl(typecast_exprt{v, integer}) == "integer(v)");
    }
  }
}
