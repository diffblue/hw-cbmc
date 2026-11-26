/*******************************************************************\

Module: VHDL Lowering Unit Tests

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/std_expr.h>

#include <testing-utils/use_catch.h>
#include <vhdl/vhdl_expr.h>
#include <vhdl/vhdl_lowering.h>
#include <vhdl/vhdl_types.h>

SCENARIO("VHDL lowering of types")
{
  GIVEN("The scalar types")
  {
    REQUIRE(vhdl_lowering(vhdl_boolean_type()) == bool_typet{});
    REQUIRE(vhdl_lowering(vhdl_bit_type()) == bool_typet{});
    REQUIRE(vhdl_lowering(vhdl_std_logic_type()) == bool_typet{});
    REQUIRE(vhdl_lowering(vhdl_integer_type()) == signedbv_typet{32});
    REQUIRE(vhdl_lowering(vhdl_natural_type()) == signedbv_typet{32});

    vhdl_enumeration_typet state{"state_t", {irept{"idle"}, irept{"run"}}};
    auto lowered = vhdl_lowering(state);
    REQUIRE(lowered.id() == ID_enumeration);
    REQUIRE(to_enumeration_type(lowered).elements().size() == 2);
  }

  GIVEN("The array types")
  {
    vhdl_ranget range{7, 0, vhdl_directiont::DOWNTO};
    REQUIRE(
      vhdl_lowering(vhdl_vector_type("std_logic_vector", range)) ==
      unsignedbv_typet{8});
    REQUIRE(
      vhdl_lowering(vhdl_vector_type("bit_vector", range)) ==
      unsignedbv_typet{8});
    REQUIRE(
      vhdl_lowering(vhdl_vector_type("unsigned", range)) ==
      unsignedbv_typet{8});
    REQUIRE(
      vhdl_lowering(vhdl_vector_type("signed", range)) == signedbv_typet{8});

    vhdl_array_typet mem{
      "mem_t", vhdl_integer_type(), {0, 3, vhdl_directiont::TO}};
    auto lowered = vhdl_lowering(mem);
    REQUIRE(lowered.id() == ID_array);
    REQUIRE(to_array_type(lowered).element_type() == signedbv_typet{32});
    REQUIRE(
      numeric_cast_v<mp_integer>(
        to_constant_expr(to_array_type(lowered).size())) == 4);
  }

  GIVEN("A record type")
  {
    vhdl_record_typet::componentst components;
    components.emplace_back("a", vhdl_bit_type());
    components.emplace_back("b", vhdl_integer_type());
    vhdl_record_typet record{"rec_t", std::move(components)};
    auto lowered = vhdl_lowering(record);
    REQUIRE(lowered.id() == ID_struct);
    REQUIRE(to_struct_type(lowered).get_component("a").type() == bool_typet{});
    REQUIRE(
      to_struct_type(lowered).get_component("b").type() == signedbv_typet{32});
  }

  GIVEN("A CBMC type")
  {
    REQUIRE(vhdl_lowering(bool_typet{}) == bool_typet{});
  }
}

SCENARIO("VHDL lowering of expressions")
{
  const vhdl_ranget range{3, 0, vhdl_directiont::DOWNTO};
  const auto slv = vhdl_vector_type("std_logic_vector", range);
  const auto u = vhdl_vector_type("unsigned", range);
  const symbol_exprt v{"v", slv};
  const symbol_exprt n{"n", vhdl_integer_type()};

  GIVEN("Constants")
  {
    REQUIRE(
      vhdl_lowering(constant_exprt{"'1'", vhdl_bit_type()}) == true_exprt{});
    REQUIRE(
      vhdl_lowering(constant_exprt{"'0'", vhdl_std_logic_type()}) ==
      false_exprt{});

    // 'L' is a distinct value of std_ulogic, and only supported where
    // it is read as '0', by the condition operator
    REQUIRE_THROWS(vhdl_lowering(constant_exprt{"'L'", vhdl_std_logic_type()}));
    REQUIRE(
      vhdl_lowering(typecast_exprt{
        constant_exprt{"'L'", vhdl_std_logic_type()}, vhdl_boolean_type()}) ==
      false_exprt{});
    REQUIRE(
      vhdl_lowering(constant_exprt{"true", vhdl_boolean_type()}) ==
      true_exprt{});
    REQUIRE(
      vhdl_lowering(vhdl_integer_constant(-3, vhdl_integer_type())) ==
      from_integer(-3, signedbv_typet{32}));

    // an array value "1010", most significant bit first
    multi_ary_exprt bits{
      ID_array,
      {constant_exprt{"'1'", vhdl_std_logic_type()},
       constant_exprt{"'0'", vhdl_std_logic_type()},
       constant_exprt{"'1'", vhdl_std_logic_type()},
       constant_exprt{"'0'", vhdl_std_logic_type()}},
      slv};
    REQUIRE(vhdl_lowering(bits) == from_integer(10, unsignedbv_typet{4}));
  }

  GIVEN("A symbol")
  {
    auto lowered = vhdl_lowering(v);
    REQUIRE(lowered.id() == ID_symbol);
    REQUIRE(lowered.type() == unsignedbv_typet{4});
  }

  GIVEN("Indexing and slicing (IEEE 1076-2008 8.4, 8.5)")
  {
    // v(3) is the most significant bit of v(3 downto 0)
    binary_exprt index{
      v,
      ID_index,
      vhdl_integer_constant(3, vhdl_integer_type()),
      vhdl_std_logic_type()};
    auto lowered = vhdl_lowering(index);
    REQUIRE(lowered.id() == ID_extractbit);
    REQUIRE(
      to_extractbit_expr(lowered).index() ==
      from_integer(3, signedbv_typet{32}));

    // v(2 downto 1)
    vhdl_slice_exprt slice{
      v,
      vhdl_range_exprt{
        vhdl_integer_constant(2, vhdl_integer_type()),
        ID_vhdl_downto,
        vhdl_integer_constant(1, vhdl_integer_type())}};
    slice.type() =
      vhdl_vector_type("std_logic_vector", {2, 1, vhdl_directiont::DOWNTO});
    auto lowered_slice = vhdl_lowering(slice);
    REQUIRE(lowered_slice.id() == ID_extractbits);
    REQUIRE(
      numeric_cast_v<mp_integer>(
        to_constant_expr(to_extractbits_expr(lowered_slice).index())) == 1);
    REQUIRE(lowered_slice.type() == unsignedbv_typet{2});

    // with a "to" range, the left-most element is the most significant bit
    auto to_type = vhdl_vector_type("bit_vector", {0, 3, vhdl_directiont::TO});
    symbol_exprt w{"w", to_type};
    binary_exprt to_index{
      w,
      ID_index,
      vhdl_integer_constant(0, vhdl_integer_type()),
      vhdl_bit_type()};
    REQUIRE(
      to_extractbit_expr(vhdl_lowering(to_index)).index() ==
      from_integer(3, signedbv_typet{32}));
  }

  GIVEN("Relational operators")
  {
    // the predefined operators on arrays are lexicographic
    symbol_exprt a{
      "a", vhdl_vector_type("bit_vector", {2, 0, vhdl_directiont::DOWNTO})};
    symbol_exprt b{
      "b", vhdl_vector_type("bit_vector", {1, 0, vhdl_directiont::DOWNTO})};
    binary_relation_exprt lt{a, ID_lt, b};
    lt.type() = vhdl_boolean_type();
    auto lowered = vhdl_lowering(lt);
    REQUIRE(lowered.type() == bool_typet{});
    REQUIRE(lowered.id() == ID_or); // prefix less, or equal and shorter

    // arrays of different lengths are not equal
    binary_relation_exprt eq{a, ID_equal, b};
    eq.type() = vhdl_boolean_type();
    REQUIRE(vhdl_lowering(eq) == false_exprt{});

    // numeric_std compares at full precision
    symbol_exprt un{"un", u};
    binary_relation_exprt numeric{
      un, ID_equal, vhdl_integer_constant(300, vhdl_integer_type())};
    numeric.type() = vhdl_boolean_type();
    auto lowered_numeric = vhdl_lowering(numeric);
    REQUIRE(lowered_numeric.id() == ID_equal);
    REQUIRE(to_equal_expr(lowered_numeric).lhs().type() == signedbv_typet{33});
  }

  GIVEN("Arithmetic")
  {
    // integer mod follows the sign of the right operand
    binary_exprt mod{
      n,
      ID_mod,
      vhdl_integer_constant(3, vhdl_integer_type()),
      vhdl_integer_type()};
    // the sum is computed one bit wider, and the result cast back
    auto lowered = vhdl_lowering(mod);
    REQUIRE(lowered.id() == ID_typecast);
    REQUIRE(lowered.type() == signedbv_typet{32});
    auto &wide_mod = to_typecast_expr(lowered).op();
    REQUIRE(wide_mod.id() == ID_mod);
    REQUIRE(wide_mod.type() == signedbv_typet{33});
    REQUIRE(to_binary_expr(wide_mod).lhs().id() == ID_plus);

    // division is done at the width of the wider operand, then resized
    symbol_exprt wide_u{
      "wu", vhdl_vector_type("unsigned", {7, 0, vhdl_directiont::DOWNTO})};
    symbol_exprt narrow_u{"nu", u};
    binary_exprt div{narrow_u, ID_div, wide_u, u}; // L'length
    auto lowered_div = vhdl_lowering(div);
    REQUIRE(lowered_div.id() == ID_typecast);
    REQUIRE(lowered_div.type() == unsignedbv_typet{4});
    REQUIRE(to_typecast_expr(lowered_div).op().type() == unsignedbv_typet{8});

    // numeric_std multiplication extends the operands to the result
    symbol_exprt un{"un", u};
    auto wide = vhdl_vector_type("unsigned", {7, 0, vhdl_directiont::DOWNTO});
    binary_exprt mult{un, ID_mult, un, wide};
    auto lowered_mult = vhdl_lowering(mult);
    REQUIRE(lowered_mult.type() == unsignedbv_typet{8});
    REQUIRE(to_binary_expr(lowered_mult).lhs().id() == ID_typecast);
  }

  GIVEN("Logical operators and concatenation")
  {
    binary_exprt and_v{v, ID_and, v, slv};
    REQUIRE(vhdl_lowering(and_v).id() == ID_bitand);

    binary_exprt and_b{
      constant_exprt{"'1'", vhdl_bit_type()},
      ID_and,
      constant_exprt{"'0'", vhdl_bit_type()},
      vhdl_bit_type()};
    REQUIRE(vhdl_lowering(and_b) == and_exprt{true_exprt{}, false_exprt{}});

    concatenation_exprt concat{
      constant_exprt{"'1'", vhdl_std_logic_type()},
      v,
      vhdl_vector_type("std_logic_vector", {0, 4, vhdl_directiont::TO})};
    auto lowered = vhdl_lowering(concat);
    REQUIRE(lowered.id() == ID_concatenation);
    REQUIRE(lowered.type() == unsignedbv_typet{5});
  }

  GIVEN("A partial assignment, as produced by the synthesis")
  {
    with_exprt with{
      v,
      vhdl_integer_constant(0, vhdl_integer_type()),
      constant_exprt{"'1'", vhdl_std_logic_type()}};
    with.type() = slv;
    auto lowered = vhdl_lowering(with);
    REQUIRE(lowered.id() == ID_update_bit);
    REQUIRE(lowered.type() == unsignedbv_typet{4});
  }
}
