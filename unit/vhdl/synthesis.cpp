/*******************************************************************\

Module: VHDL Synthesis Unit Tests

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/mathematical_expr.h>
#include <util/message.h>
#include <util/symbol_table.h>

#include <testing-utils/use_catch.h>
#include <trans-word-level/next_symbol.h>
#include <vhdl/vhdl_parser.h>
#include <vhdl/vhdl_synthesis.h>
#include <vhdl/vhdl_typecheck.h>
#include <vhdl/vhdl_types.h>

#include <sstream>

/// parse, type check and synthesise the given VHDL text for the
/// given entity; returns the transition system expression, which has
/// VHDL types, as the lowering is a separate pass
static transt synthesise(
  const std::string &text,
  const std::string &entity,
  symbol_tablet &symbol_table)
{
  null_message_handlert message_handler;
  vhdl_parsert parser{message_handler};
  std::istringstream in{text};
  parser.set_file("test.vhd");
  parser.in = &in;
  parser.grammar = vhdl_parsert::LANGUAGE;
  REQUIRE(!parser.parse());

  REQUIRE(!vhdl_typecheck(
    parser.parse_tree,
    symbol_table,
    entity,
    default_vhdl_standard,
    message_handler));

  const std::string module = "vhdl::" + entity;
  REQUIRE(!vhdl_synthesis(symbol_table, module, message_handler));

  return to_trans_expr(symbol_table.lookup_ref(module).value);
}

/// does the conjunction contain the given conjunct?
static bool has_conjunct(const exprt &conjunction, const exprt &conjunct)
{
  if(conjunction == conjunct)
    return true;
  if(conjunction.id() == ID_and)
    for(auto &op : conjunction.operands())
      if(has_conjunct(op, conjunct))
        return true;
  return false;
}

SCENARIO("VHDL synthesis")
{
  GIVEN("A clocked process with a register")
  {
    symbol_tablet symbol_table;
    auto trans = synthesise(
      "entity e is port(clk : in bit; d : in bit); end;\n"
      "architecture rtl of e is\n"
      "  signal q : bit := '0';\n"
      "  signal w : bit;\n"
      "begin\n"
      "  process(clk) begin\n"
      "    if clk'event and clk = '1' then q <= d; end if;\n"
      "  end process;\n"
      "  w <= not q;\n"
      "  p: assert w /= q;\n"
      "end;\n",
      "e",
      symbol_table);

    auto &q = symbol_table.lookup_ref("vhdl::e.q");
    auto &d = symbol_table.lookup_ref("vhdl::e.d");
    auto &w = symbol_table.lookup_ref("vhdl::e.w");
    auto &clk = symbol_table.lookup_ref("vhdl::e.clk");

    THEN("inputs and state variables are flagged")
    {
      REQUIRE(d.is_input);
      REQUIRE(!d.is_state_var);
      REQUIRE(clk.is_input);
      REQUIRE(q.is_state_var);
      REQUIRE(!q.is_input);
    }

    THEN("the register has a next-state function in TRANS")
    {
      symbol_exprt q_expr{q.name, q.type};
      symbol_exprt d_expr{d.name, d.type};
      REQUIRE(has_conjunct(
        trans.trans(), equal_exprt{next_symbol_exprt{q_expr}, d_expr}));
    }

    THEN("the initial value is in INIT")
    {
      symbol_exprt q_expr{q.name, q.type};
      REQUIRE(q.type == vhdl_bit_type());
      constant_exprt zero{"'0'", q.type};
      REQUIRE(has_conjunct(trans.init(), equal_exprt{q_expr, zero}));
    }

    THEN("the concurrent assignment is in INVAR")
    {
      symbol_exprt q_expr{q.name, q.type};
      symbol_exprt w_expr{w.name, w.type};
      exprt not_q = unary_exprt{ID_not, q_expr, w.type};
      REQUIRE(has_conjunct(trans.invar(), equal_exprt{w_expr, not_q}));
    }

    THEN("the assertion is a property named after its label")
    {
      auto &property = symbol_table.lookup_ref("vhdl::e.p");
      REQUIRE(property.is_property);
      REQUIRE(property.pretty_name == "e.p");
      REQUIRE(property.value.id() == ID_G);
    }
  }

  GIVEN("A process variable")
  {
    symbol_tablet symbol_table;
    auto trans = synthesise(
      "entity e is port(clk : in bit; a : in integer); end;\n"
      "architecture rtl of e is\n"
      "  signal s : integer := 0;\n"
      "begin\n"
      "  process(clk)\n"
      "    variable t : integer := 0;\n"
      "  begin\n"
      "    if clk'event and clk = '1' then\n"
      "      t := a;\n"
      "      t := t + a;\n" // the variable sees the new value immediately
      "      s <= t;\n"
      "    end if;\n"
      "  end process;\n"
      "end;\n",
      "e",
      symbol_table);

    auto &s = symbol_table.lookup_ref("vhdl::e.s");
    auto &a = symbol_table.lookup_ref("vhdl::e.a");
    auto &t = symbol_table.lookup_ref("vhdl::e.process#1.t");

    THEN("the variable is a state variable, marked auxiliary")
    {
      REQUIRE(t.is_state_var);
      REQUIRE(t.is_auxiliary);
    }

    THEN("the signal gets a + a, not t + a")
    {
      symbol_exprt s_expr{s.name, s.type};
      symbol_exprt a_expr{a.name, a.type};
      REQUIRE(s.type == vhdl_integer_type());
      exprt sum = binary_exprt{a_expr, ID_plus, a_expr, s.type};
      REQUIRE(has_conjunct(
        trans.trans(), equal_exprt{next_symbol_exprt{s_expr}, sum}));
    }
  }
}
