/*******************************************************************\

Module: VHDL Type Unit Tests

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>

#include <testing-utils/use_catch.h>
#include <vhdl/vhdl_types.h>

SCENARIO("VHDL ranges")
{
  GIVEN("A downto range")
  {
    vhdl_ranget range{7, 0, vhdl_directiont::DOWNTO};
    REQUIRE(range.low() == 0);
    REQUIRE(range.high() == 7);
    REQUIRE(range.length() == 8);
    REQUIRE(range.position(0) == 0);
    REQUIRE(range.to_string() == "7 downto 0");
  }

  GIVEN("A to range")
  {
    vhdl_ranget range{2, 5, vhdl_directiont::TO};
    REQUIRE(range.low() == 2);
    REQUIRE(range.high() == 5);
    REQUIRE(range.length() == 4);
    REQUIRE(range.position(2) == 0);
    REQUIRE(range.position(5) == 3);
    REQUIRE(range.to_string() == "2 to 5");
  }

  GIVEN("A null range (IEEE 1076-2008 5.2.1)")
  {
    vhdl_ranget range{1, 0, vhdl_directiont::TO};
    REQUIRE(range.length() == 0);
  }
}

SCENARIO("VHDL types")
{
  GIVEN("The predefined enumeration types")
  {
    auto boolean = vhdl_boolean_type();
    REQUIRE(boolean.id() == ID_vhdl_enumeration);
    REQUIRE(boolean.name() == "boolean");
    REQUIRE(boolean.elements().size() == 2);
    REQUIRE(boolean.position("true") == 1);
    REQUIRE(!boolean.position("'1'").has_value());

    // character literals are keyed with their quotes, apart from
    // identifiers and case sensitive
    REQUIRE(vhdl_bit_type().position("'1'") == 1);
    REQUIRE(vhdl_enumeration_typet::character_literal('Z') == "'Z'");
    REQUIRE(vhdl_enumeration_typet::is_character_literal("'Z'"));
    REQUIRE(!vhdl_enumeration_typet::is_character_literal("z"));
    REQUIRE(boolean.literal(0) == "false");

    REQUIRE(is_vhdl_scalar_bit_type(vhdl_std_logic_type()));
    REQUIRE(is_vhdl_scalar_bit_type(vhdl_bit_type()));
    REQUIRE(!is_vhdl_scalar_bit_type(vhdl_boolean_type()));

    // IEEE 1076-2008 std_logic_1164: std_logic is a subtype of std_ulogic
    auto std_logic = vhdl_std_logic_type();
    REQUIRE(std_logic.name() == "std_logic");
    REQUIRE(std_logic.base_name() == "std_ulogic");
    REQUIRE(std_logic.elements().size() == 9);
    REQUIRE(std_logic.position("'H'") == 7);
  }

  GIVEN("The integer types")
  {
    auto integer = vhdl_integer_type();
    REQUIRE(integer.id() == ID_vhdl_integer);
    REQUIRE(is_vhdl_integer_type(integer));
    REQUIRE(integer.range().low() == -power(2, 31));
    REQUIRE(integer.range().high() == power(2, 31) - 1);

    auto natural = vhdl_natural_type();
    REQUIRE(natural.name() == "natural");
    REQUIRE(natural.base_name() == "integer");
    REQUIRE(natural.range().low() == 0);

    auto small = vhdl_integer_type({0, 7, vhdl_directiont::TO});
    REQUIRE(small.range().length() == 8);
    REQUIRE(vhdl_type_to_string(small) == "integer range 0 to 7");
    REQUIRE(vhdl_type_to_string(integer) == "integer");
    REQUIRE(vhdl_type_to_string(vhdl_positive_type()) == "positive");

    auto c = vhdl_integer_constant(-5, integer);
    REQUIRE(vhdl_integer_value(c) == -5);
  }

  GIVEN("The vector types")
  {
    vhdl_ranget range{7, 0, vhdl_directiont::DOWNTO};
    auto slv = vhdl_vector_type("std_logic_vector", range);
    auto u = vhdl_vector_type("unsigned", range);
    auto s = vhdl_vector_type("signed", range);
    REQUIRE(is_vhdl_vector_type(slv));
    REQUIRE(is_vhdl_vector_type(u));
    REQUIRE(is_vhdl_vector_type(s));
    REQUIRE(!is_vhdl_numeric_vector_type(slv));
    REQUIRE(is_vhdl_numeric_vector_type(u));
    REQUIRE(is_vhdl_numeric_vector_type(s));
    REQUIRE(!is_vhdl_integer_type(s));
    REQUIRE(slv.is_constrained());
    REQUIRE(slv.length() == 8);
    REQUIRE(slv.range().direction == vhdl_directiont::DOWNTO);
    REQUIRE(slv.element_type() == vhdl_std_logic_type());
    REQUIRE(
      vhdl_vector_type("bit_vector", range).element_type() == vhdl_bit_type());
    REQUIRE(vhdl_type_to_string(slv) == "std_logic_vector(7 downto 0)");

    auto unconstrained = vhdl_unconstrained_array_type("unsigned");
    REQUIRE(!unconstrained.is_constrained());
    REQUIRE(!is_vhdl_vector_type(unconstrained));
    REQUIRE(vhdl_type_to_string(unconstrained) == "unsigned");
    REQUIRE(vhdl_constrained_array_type(unconstrained, range) == u);
    REQUIRE(u.unconstrained() == unconstrained);
    REQUIRE(is_unconstrained_array(unconstrained));
    REQUIRE(!is_unconstrained_array(u));

    // the index subtype of the predefined vectors is natural, so a
    // value without a range from the context gets 0 to N-1
    REQUIRE(unconstrained.index_type() == vhdl_natural_type());
    auto literal_range = unconstrained.range_for_length(4);
    REQUIRE(literal_range.left == 0);
    REQUIRE(literal_range.right == 3);
    REQUIRE(literal_range.direction == vhdl_directiont::TO);

    // array (positive range <>) of bit
    vhdl_array_typet pvec{"pvec", vhdl_bit_type(), vhdl_positive_type()};
    REQUIRE(pvec.range_for_length(2).left == 1);
    REQUIRE(pvec.range_for_length(2).right == 2);

    // array (d range <>) of bit, with a descending d
    vhdl_array_typet dvec{
      "dvec",
      vhdl_bit_type(),
      vhdl_integer_type({5, 0, vhdl_directiont::DOWNTO})};
    auto d_range = dvec.range_for_length(3);
    REQUIRE(d_range.left == 5);
    REQUIRE(d_range.right == 3);
    REQUIRE(d_range.direction == vhdl_directiont::DOWNTO);
  }

  GIVEN("A user-defined array and a record type")
  {
    vhdl_array_typet mem{
      "mem_t", vhdl_integer_type(), {0, 3, vhdl_directiont::TO}};
    REQUIRE(!is_vhdl_vector_type(mem));
    REQUIRE(mem.element_type() == vhdl_integer_type());
    REQUIRE(vhdl_type_to_string(mem) == "mem_t(0 to 3)");

    vhdl_record_typet::componentst components;
    components.emplace_back("a", vhdl_bit_type());
    components.emplace_back("b", vhdl_integer_type());
    vhdl_record_typet record{"rec_t", std::move(components)};
    REQUIRE(record.has_component("b"));
    REQUIRE(!record.has_component("c"));
    REQUIRE(record.get_component("a").type() == vhdl_bit_type());
    REQUIRE(vhdl_type_to_string(record) == "rec_t");
  }

  GIVEN("Type compatibility (IEEE 1076-2008 5.1)")
  {
    vhdl_ranget range{7, 0, vhdl_directiont::DOWNTO};
    auto slv = vhdl_vector_type("std_logic_vector", range);
    auto sulv = vhdl_vector_type("std_ulogic_vector", range);
    auto u = vhdl_vector_type("unsigned", range);

    THEN("the same type is compatible with itself")
    {
      REQUIRE(vhdl_types_compatible(slv, slv));
    }

    THEN("integer and its subtypes are compatible")
    {
      REQUIRE(vhdl_types_compatible(vhdl_integer_type(), vhdl_natural_type()));
      REQUIRE(vhdl_types_compatible(
        vhdl_integer_type(), vhdl_integer_type({0, 15, vhdl_directiont::TO})));
    }

    THEN("std_logic is a subtype of std_ulogic")
    {
      REQUIRE(
        vhdl_types_compatible(vhdl_std_logic_type(), vhdl_std_ulogic_type()));
      REQUIRE(vhdl_types_compatible(slv, sulv));
    }

    THEN("distinct types are incompatible even when the values agree")
    {
      REQUIRE(
        !vhdl_types_compatible(vhdl_boolean_type(), vhdl_std_logic_type()));
      REQUIRE(!vhdl_types_compatible(vhdl_bit_type(), vhdl_std_logic_type()));
      REQUIRE(!vhdl_types_compatible(slv, u));
    }

    THEN("subtypes with different constraints are compatible")
    {
      auto narrow =
        vhdl_vector_type("std_logic_vector", {3, 0, vhdl_directiont::DOWNTO});
      REQUIRE(vhdl_types_compatible(slv, narrow));
      REQUIRE(slv != narrow);
    }

    THEN("a user-defined type is distinct from its base type")
    {
      auto small = vhdl_integer_type({0, 7, vhdl_directiont::TO});
      small.set_name("small");
      REQUIRE(small.base_name() == "integer");
      REQUIRE(vhdl_types_compatible(small, vhdl_integer_type()));

      vhdl_integer_typet my_int{"my_int", {0, 7, vhdl_directiont::TO}};
      REQUIRE(!vhdl_types_compatible(my_int, vhdl_integer_type()));
    }
  }

  GIVEN("Universal types")
  {
    REQUIRE(is_vhdl_universal_type(typet{ID_natural}));
    REQUIRE(is_vhdl_universal_type(typet{ID_char}));
    REQUIRE(is_vhdl_universal_type(typet{ID_string}));
    REQUIRE(is_vhdl_universal_type(typet{ID_vhdl_overloaded_literal}));
    REQUIRE(!is_vhdl_universal_type(vhdl_integer_type()));
  }
}
