/*******************************************************************\

Module: VHDL Expression Class Unit Tests

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/mathematical_types.h>
#include <util/std_expr.h>

#include <testing-utils/use_catch.h>
#include <vhdl/vhdl_expr.h>
#include <vhdl/vhdl_types.h>

SCENARIO("VHDL expression classes")
{
  const symbol_exprt v{"v", typet{}};
  const exprt zero = from_integer(0, integer_typet{});
  const exprt seven = from_integer(7, integer_typet{});

  GIVEN("A range")
  {
    vhdl_range_exprt range{seven, ID_vhdl_downto, zero};
    REQUIRE(range.id() == ID_range);
    REQUIRE(range.left() == seven);
    REQUIRE(range.right() == zero);
    REQUIRE(range.direction() == ID_vhdl_downto);
    REQUIRE(
      to_vhdl_range_expr(static_cast<const exprt &>(range)).left() == seven);
  }

  GIVEN("A slice")
  {
    vhdl_slice_exprt slice{v, vhdl_range_exprt{seven, ID_vhdl_downto, zero}};
    REQUIRE(slice.prefix() == v);
    REQUIRE(slice.range().id() == ID_range);
  }

  GIVEN("An indexed name with arguments")
  {
    vhdl_indexed_exprt indexed{v};
    indexed.add_argument(vhdl_associationt{nil_exprt{}, zero});
    indexed.add_argument(vhdl_associationt{symbol_exprt{"f", typet{}}, seven});
    REQUIRE(indexed.prefix() == v);
    REQUIRE(indexed.number_of_arguments() == 2);
    REQUIRE(!indexed.argument(0).is_named());
    REQUIRE(indexed.argument(0).actual() == zero);
    REQUIRE(indexed.argument(1).is_named());
    REQUIRE(indexed.argument(1).formal().get(ID_identifier) == "f");
  }

  GIVEN("An attribute name")
  {
    vhdl_attribute_exprt attribute{v, "LENGTH"};
    REQUIRE(attribute.prefix() == v);
    REQUIRE(attribute.attribute() == "LENGTH");
  }

  GIVEN("An aggregate")
  {
    vhdl_aggregate_exprt aggregate;
    vhdl_element_associationt others{zero};
    others.choices().push_back(irept{ID_vhdl_others});
    aggregate.add_association(vhdl_element_associationt{seven});
    aggregate.add_association(std::move(others));
    REQUIRE(aggregate.operands().size() == 2);
    REQUIRE(aggregate.association(0).is_positional());
    REQUIRE(aggregate.association(0).value() == seven);
    REQUIRE(!aggregate.association(1).is_positional());
  }

  GIVEN("A selected assignment")
  {
    vhdl_selected_assignt selected{v, zero, true};
    REQUIRE(selected.target() == v);
    REQUIRE(selected.selector() == zero);
    REQUIRE(selected.is_variable_assignment());
    REQUIRE(selected.alternatives().empty());
  }

  GIVEN("A subtype indication")
  {
    vhdl_subtype_indicationt subtype{symbol_exprt{"integer", typet{}}};
    REQUIRE(!subtype.has_constraint());
    subtype.range_constraint(vhdl_range_exprt{zero, ID_to, seven});
    REQUIRE(subtype.has_constraint());
    REQUIRE(subtype.type_mark().get(ID_identifier) == "integer");
    REQUIRE(subtype.index_constraint().empty());
  }
}
