/*******************************************************************\

Module: Verilog Bit-Level Layout Unit Tests

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <testing-utils/use_catch.h>
#include <verilog/verilog_layout.h>
#include <verilog/verilog_lowering.h>
#include <verilog/verilog_types.h>

static verilog_array_typet
array_type(irep_idt kind, mp_integer size, mp_integer offset, bool increasing)
{
  return verilog_array_typet{
    kind, unsignedbv_typet{8}, size, offset, increasing};
}

SCENARIO("vector bit ranges")
{
  // reg [7:0]
  auto decreasing = verilog_vector_bit_range(8, 0, false, 2, 4);
  REQUIRE(decreasing.lower == 2);
  REQUIRE(decreasing.upper == 4);

  // reg [8:1]: declared index 1 is bit 0
  auto with_offset = verilog_vector_bit_range(8, 1, false, 1, 1);
  REQUIRE(with_offset.lower == 0);
  REQUIRE(with_offset.upper == 0);

  // reg [0:7]: declared index 0 is the most significant bit
  auto increasing = verilog_vector_bit_range(8, 0, true, 0, 2);
  REQUIRE(increasing.lower == 5);
  REQUIRE(increasing.upper == 7);

  // out of range lies outside of the vector
  auto outside = verilog_vector_bit_range(8, 0, false, 9, 9);
  REQUIRE(outside.lower == 9);
}

SCENARIO("unpacked array layout")
{
  // int a [3:0], int b [0:3], elements start at the left index
  auto decreasing = array_type(ID_verilog_unpacked_array, 4, 0, false);
  REQUIRE(verilog_unpacked_array_element_index(decreasing, 3) == 0);
  REQUIRE(verilog_unpacked_array_element_index(decreasing, 0) == 3);
  REQUIRE(verilog_unpacked_array_element_index(decreasing, 4) == -1);

  auto increasing = array_type(ID_verilog_unpacked_array, 4, 0, true);
  REQUIRE(verilog_unpacked_array_element_index(increasing, 0) == 0);
  REQUIRE(verilog_unpacked_array_element_index(increasing, 3) == 3);

  auto with_offset = array_type(ID_verilog_unpacked_array, 4, 2, false);
  REQUIRE(verilog_unpacked_array_element_index(with_offset, 5) == 0);

  REQUIRE(!verilog_array_element_zero_is_msb(increasing));
  REQUIRE(verilog_array_element_lower_bit(increasing, 2) == 16);
}

SCENARIO("packed array layout")
{
  // logic [3:0][7:0] a: a[0] is the least significant byte
  auto decreasing = array_type(ID_verilog_packed_array, 4, 0, false);
  REQUIRE(!verilog_array_element_zero_is_msb(decreasing));
  REQUIRE(verilog_packed_array_lower_bit(decreasing, 0, 0) == 0);
  REQUIRE(verilog_packed_array_lower_bit(decreasing, 1, 2) == 8);
  REQUIRE(verilog_array_element_lower_bit(decreasing, 1) == 8);

  // logic [0:3][7:0] a: a[0] is the most significant byte
  auto increasing = array_type(ID_verilog_packed_array, 4, 0, true);
  REQUIRE(verilog_array_element_zero_is_msb(increasing));
  REQUIRE(verilog_packed_array_lower_bit(increasing, 0, 0) == 24);
  REQUIRE(verilog_packed_array_lower_bit(increasing, 1, 2) == 8);
  REQUIRE(verilog_array_element_lower_bit(increasing, 0) == 24);
  REQUIRE(verilog_array_element_lower_bit(increasing, 3) == 0);
}

SCENARIO("struct and union layout")
{
  struct_union_typet::componentst components;
  components.emplace_back("a", unsignedbv_typet{3});
  components.emplace_back("b", unsignedbv_typet{5});

  struct_typet struct_type{components};

  // the first member is the most significant
  auto lower_bits = verilog_struct_component_lower_bits(struct_type);
  REQUIRE(lower_bits.size() == 2);
  REQUIRE(lower_bits[0] == 5);
  REQUIRE(lower_bits[1] == 0);

  auto a = verilog_member_bit_range(struct_type, "a");
  REQUIRE(a.has_value());
  REQUIRE(a->lower == 5);
  REQUIRE(a->upper == 7);
  REQUIRE(!verilog_member_bit_range(struct_type, "c").has_value());

  // all members of a union start at bit 0
  verilog_union_typet union_type{true, components};
  auto b = verilog_member_bit_range(union_type, "b");
  REQUIRE(b.has_value());
  REQUIRE(b->lower == 0);
  REQUIRE(b->upper == 4);

  REQUIRE(!verilog_member_bit_range(unsignedbv_typet{8}, "a").has_value());
}

SCENARIO("layout agrees with to_bitvector")
{
  // to_bitvector concatenates, most significant operand first. The k-th
  // operand must start at the bit given by the layout.
  GIVEN("packed arrays of both directions")
  {
    for(bool increasing : {false, true})
    {
      auto type = array_type(ID_verilog_packed_array, 4, 0, increasing);
      auto bv = to_bitvector(symbol_exprt{"a", type});

      REQUIRE(bv.id() == ID_concatenation);
      REQUIRE(bv.operands().size() == 4);

      for(std::size_t k = 0; k < 4; k++)
      {
        auto &element = to_index_expr(bv.operands()[k]);
        auto array_index =
          numeric_cast_v<mp_integer>(to_constant_expr(element.index()));
        REQUIRE(
          verilog_array_element_lower_bit(type, array_index) == (3 - k) * 8);
      }
    }
  }

  GIVEN("a packed struct")
  {
    struct_union_typet::componentst components;
    components.emplace_back("a", unsignedbv_typet{3});
    components.emplace_back("b", unsignedbv_typet{5});
    struct_typet struct_type{components};

    auto bv = to_bitvector(symbol_exprt{"s", struct_type});
    REQUIRE(bv.id() == ID_concatenation);
    REQUIRE(bv.operands().size() == 2);

    mp_integer position = 8;
    for(std::size_t k = 0; k < 2; k++)
    {
      auto &member = to_member_expr(bv.operands()[k]);
      auto range =
        verilog_member_bit_range(struct_type, member.get_component_name());
      REQUIRE(range.has_value());
      position -= range->width();
      REQUIRE(range->lower == position);
    }
  }
}
