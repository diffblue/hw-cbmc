/*******************************************************************\

Module: VHDL Expression Class Unit Tests

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/mathematical_types.h>
#include <util/std_expr.h>
#include <util/std_types.h>

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

  GIVEN("A labelled statement")
  {
    vhdl_signal_assignt assignment{v, zero};
    REQUIRE(!assignment.has_label());

    // the label is set through the statement base class, as the parser
    // does for any kind of statement
    exprt &as_expr = assignment;
    to_vhdl_statement(as_expr).set_label("L1");
    REQUIRE(assignment.has_label());
    REQUIRE(assignment.label() == "L1");
    REQUIRE(to_vhdl_signal_assign(as_expr).label() == "L1");
    REQUIRE(to_vhdl_signal_assign(as_expr).target() == v);

    vhdl_processt process{nil_exprt{}, irept{}, code_blockt{}};
    REQUIRE(process.label().empty());
    REQUIRE(process.body().id() == ID_code);
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

  GIVEN("An overloaded enumeration literal")
  {
    enumeration_typet s1, s2;
    s1.elements().push_back(irept{"idle"});
    s2.elements().push_back(irept{"idle"});
    vhdl_overloaded_literal_exprt literal{
      "Idle", {constant_exprt{"idle", s1}, constant_exprt{"idle", s2}}};
    REQUIRE(literal.identifier() == "Idle");
    REQUIRE(literal.candidates().size() == 2);
    REQUIRE(literal.candidates()[1].type() == s2);
    REQUIRE(is_vhdl_universal_type(literal.type()));
    REQUIRE(
      to_vhdl_overloaded_literal_expr(static_cast<const exprt &>(literal))
        .identifier() == "Idle");
  }

  GIVEN("A type checked assertion")
  {
    constant_exprt report{"fail", typet{ID_string}};
    vhdl_code_assertt assertion{true_exprt{}, "p1", report};
    REQUIRE(assertion.get_statement() == ID_assert);
    REQUIRE(assertion.condition() == true_exprt{});
    REQUIRE(assertion.label() == "p1");
    REQUIRE(assertion.report() == report);
    REQUIRE(to_vhdl_code_assert(assertion).label() == "p1");
  }

  GIVEN("A type checked assignment")
  {
    vhdl_code_assignt signal_assignment{true, v, zero};
    REQUIRE(signal_assignment.get_statement() == ID_vhdl_signal_assign);
    REQUIRE(signal_assignment.is_signal_assignment());
    REQUIRE(signal_assignment.target() == v);
    REQUIRE(signal_assignment.value() == zero);

    vhdl_code_assignt variable_assignment{false, v, seven};
    REQUIRE(variable_assignment.get_statement() == ID_assign);
    REQUIRE(!variable_assignment.is_signal_assignment());
    REQUIRE(variable_assignment.value() == seven);
    REQUIRE(to_vhdl_code_assign(variable_assignment).target() == v);
  }
}
