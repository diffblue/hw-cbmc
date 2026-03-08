/*******************************************************************\

Module: Indexed Part Select Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>

#include <testing-utils/use_catch.h>
#include <verilog/verilog_expr.h>

/// helper: make a 32-bit unsignedbv symbol with offset 0
static symbol_exprt src32(const irep_idt &name)
{
  auto type = unsignedbv_typet{32};
  type.set(ID_C_offset, "0");
  return symbol_exprt{name, std::move(type)};
}

SCENARIO("indexed part-select lower, constant index")
{
  // src[15 +: 8] — selects bits 15..22
  GIVEN("a +: part select with constant index")
  {
    auto src = src32("a");
    auto index = from_integer(15, integer_typet{});
    auto width = from_integer(8, integer_typet{});
    verilog_indexed_part_select_plus_or_minus_exprt ps(
      ID_verilog_indexed_part_select_plus,
      src,
      index,
      width,
      unsignedbv_typet{8});

    auto result = ps.lower();

    THEN("result is extractbits with bottom = 15")
    {
      REQUIRE(result.id() == ID_extractbits);
      auto &eb = to_extractbits_expr(result);
      REQUIRE(eb.src() == src);
      auto bottom = numeric_cast_v<mp_integer>(to_constant_expr(eb.index()));
      REQUIRE(bottom == 15);
    }
  }

  // src[15 -: 8] — selects bits 15..8, bottom = 8
  GIVEN("a -: part select with constant index")
  {
    auto src = src32("a");
    auto index = from_integer(15, integer_typet{});
    auto width = from_integer(8, integer_typet{});
    verilog_indexed_part_select_plus_or_minus_exprt ps(
      ID_verilog_indexed_part_select_minus,
      src,
      index,
      width,
      unsignedbv_typet{8});

    auto result = ps.lower();

    THEN("result is extractbits with bottom = 8")
    {
      REQUIRE(result.id() == ID_extractbits);
      auto &eb = to_extractbits_expr(result);
      REQUIRE(eb.src() == src);
      auto bottom = numeric_cast_v<mp_integer>(to_constant_expr(eb.index()));
      REQUIRE(bottom == 8);
    }
  }
}

SCENARIO("indexed part-select lower, non-constant index")
{
  GIVEN("a +: part select with non-constant index")
  {
    auto src = src32("a");
    auto index = symbol_exprt{"i", integer_typet{}};
    auto width = from_integer(8, integer_typet{});
    verilog_indexed_part_select_plus_or_minus_exprt ps(
      ID_verilog_indexed_part_select_plus,
      src,
      index,
      width,
      unsignedbv_typet{8});

    auto result = ps.lower();

    THEN("result is extractbits of a right-shifted source")
    {
      REQUIRE(result.id() == ID_extractbits);
      auto &eb = to_extractbits_expr(result);
      REQUIRE(eb.src().id() == ID_lshr);
    }
  }

  GIVEN("a -: part select with non-constant index")
  {
    auto src = src32("a");
    auto index = symbol_exprt{"i", integer_typet{}};
    auto width = from_integer(8, integer_typet{});
    verilog_indexed_part_select_plus_or_minus_exprt ps(
      ID_verilog_indexed_part_select_minus,
      src,
      index,
      width,
      unsignedbv_typet{8});

    auto result = ps.lower();

    THEN("result is extractbits of a right-shifted source, shifted by i - 7")
    {
      REQUIRE(result.id() == ID_extractbits);
      auto &eb = to_extractbits_expr(result);
      REQUIRE(eb.src().id() == ID_lshr);
      // The shift amount should be i - (width - 1) = i - 7
      auto &shift_rhs = to_binary_expr(eb.src()).op1();
      REQUIRE(shift_rhs.id() == ID_minus);
      auto &minus = to_minus_expr(shift_rhs);
      REQUIRE(minus.lhs() == index);
      auto rhs_val = numeric_cast_v<mp_integer>(to_constant_expr(minus.rhs()));
      REQUIRE(rhs_val == 7); // src_offset(0) + width(8) - 1
    }
  }
}
