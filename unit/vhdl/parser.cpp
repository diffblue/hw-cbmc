/*******************************************************************\

Module: VHDL Parser Unit Tests

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/message.h>

#include <testing-utils/use_catch.h>
#include <vhdl/vhdl_expr.h>
#include <vhdl/vhdl_parser.h>
#include <vhdl/vhdl_types.h>

#include <sstream>

/// parse the given VHDL text; returns the parse tree
static vhdl_parse_treet parse(const std::string &text, bool &error)
{
  null_message_handlert message_handler;
  vhdl_parsert parser{message_handler};
  std::istringstream in{text};
  parser.set_file("test.vhd");
  parser.in = &in;
  parser.grammar = vhdl_parsert::LANGUAGE;
  error = parser.parse();
  return std::move(parser.parse_tree);
}

SCENARIO("Parsing VHDL design units")
{
  GIVEN("An entity and an architecture")
  {
    bool error;
    auto parse_tree = parse(
      "library ieee;\n"
      "use ieee.std_logic_1164.all;\n"
      "entity E is\n"
      "  port(clk : in std_logic; q : out std_logic_vector(7 downto 0));\n"
      "end entity E;\n"
      "architecture rtl of E is\n"
      "  signal r : std_logic_vector(7 downto 0) := (others => '0');\n"
      "begin\n"
      "  q <= r(6 downto 0) & r(7);\n"
      "  p: process(clk) begin\n"
      "    if rising_edge(clk) then r <= not r; end if;\n"
      "  end process;\n"
      "end rtl;\n",
      error);

    REQUIRE(!error);

    THEN("the parse tree has the library, use, entity and architecture")
    {
      REQUIRE(parse_tree.items.size() == 4);
      auto it = parse_tree.items.begin();
      REQUIRE(it->is_library());
      ++it;
      REQUIRE(it->is_use());
      ++it;
      REQUIRE(it->is_entity());
      REQUIRE(it->get_identifier() == "e");
      REQUIRE(it->find(ID_ports).get_sub().size() == 2);
      ++it;
      REQUIRE(it->is_architecture());
      REQUIRE(it->get_entity_identifier() == "e");

      auto &architecture = *it;

      THEN("the port types are subtype indications with constraints")
      {
        auto port = parse_tree.items.begin();
        std::advance(port, 2);
        auto &q = port->find(ID_ports).get_sub()[1];
        auto &q_type = to_vhdl_subtype_indication(
          static_cast<const typet &>(q.find(ID_type)));
        REQUIRE(q_type.type_mark().get(ID_identifier) == "std_logic_vector");
        REQUIRE(q_type.has_constraint());
        REQUIRE(q_type.index_constraint().size() == 1);
        auto &range = to_vhdl_range_expr(
          static_cast<const exprt &>(q_type.index_constraint().front()));
        REQUIRE(range.direction() == ID_vhdl_downto);
        REQUIRE(range.left().get(ID_value) == "7");
        REQUIRE(range.right().get(ID_value) == "0");
      }

      THEN("the signal declaration has an aggregate initial value")
      {
        auto &decl = architecture.find(ID_decl).get_sub();
        REQUIRE(decl.size() == 1);
        REQUIRE(decl.front().id() == ID_signal);
        auto &init = static_cast<const exprt &>(decl.front().find(ID_init));
        REQUIRE(init.id() == ID_vhdl_aggregate);
        auto &association = to_vhdl_aggregate_expr(init).association(0);
        REQUIRE(!association.is_positional());
        REQUIRE(association.choices().front().id() == ID_vhdl_others);
      }

      THEN("the concurrent statements are a signal assignment and a process")
      {
        auto &body = architecture.find(ID_body).get_sub();
        REQUIRE(body.size() == 2);

        auto &assignment =
          to_vhdl_signal_assign(static_cast<const exprt &>(body[0]));
        REQUIRE(assignment.target().get(ID_identifier) == "q");
        REQUIRE(assignment.value().id() == ID_concatenation);
        auto &slice = to_vhdl_slice_expr(assignment.value().operands()[0]);
        REQUIRE(slice.prefix().get(ID_identifier) == "r");
        REQUIRE(
          to_vhdl_range_expr(slice.range()).direction() == ID_vhdl_downto);
        auto &indexed = to_vhdl_indexed_expr(assignment.value().operands()[1]);
        REQUIRE(indexed.number_of_arguments() == 1);
        REQUIRE(!indexed.argument(0).is_named());

        auto &process = to_vhdl_process(static_cast<const exprt &>(body[1]));
        REQUIRE(process.get(ID_label) == "p");
        REQUIRE(process.sensitivity().get_sub().size() == 1);
        REQUIRE(process.body().id() == ID_block);
        REQUIRE(process.body().operands().size() == 1);
        REQUIRE(process.body().operands()[0].id() == ID_ifthenelse);
      }
    }
  }

  GIVEN("A character literal after an identifier and after an operator")
  {
    // IEEE 1076-2008 15.6: the tick after a name is an attribute,
    // a tick elsewhere starts a character literal
    bool error;
    auto parse_tree = parse(
      "entity e is end;\n"
      "architecture a of e is\n"
      "  signal x : bit;\n"
      "begin\n"
      "  x <= bit'('1');\n"
      "  assert x'event or x = '0';\n"
      "end;\n",
      error);

    REQUIRE(!error);
    auto &architecture = parse_tree.items.back();
    auto &body = architecture.find(ID_body).get_sub();
    REQUIRE(body.size() == 2);
    auto &assignment =
      to_vhdl_signal_assign(static_cast<const exprt &>(body[0]));
    auto &qualified = to_vhdl_qualified_expr(assignment.value());
    REQUIRE(qualified.type_mark().get(ID_identifier) == "bit");
    REQUIRE(qualified.op().get(ID_value) == "1");
  }

  GIVEN("A syntax error")
  {
    bool error;
    parse(
      "entity e is end;\narchitecture a of e is begin x <= ; end;\n", error);
    REQUIRE(error);
  }

  GIVEN("Non-associative relational operators")
  {
    // IEEE 1076-2008 9.1: a = b = c is not an expression
    bool error;
    parse(
      "entity e is end;\n"
      "architecture a of e is begin assert a = b = c; end;\n",
      error);
    REQUIRE(error);
  }
}
