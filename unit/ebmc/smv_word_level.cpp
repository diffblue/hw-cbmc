/*******************************************************************\

Module: Word-Level SMV Output Unit Tests

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/std_expr.h>

#include <ebmc/ebmc_properties.h>
#include <ebmc/output_smv_word_level.h>
#include <ebmc/transition_system.h>
#include <testing-utils/use_catch.h>

#include <sstream>

/// Build a transition system for module 'main'. The variables in `inputs`
/// are declared but otherwise unconstrained; each wire in `wires` is both
/// declared and constrained by an INVAR of the form `name = value`. This
/// mirrors what the Verilog front-end produces for continuous assignments
/// to wires, which is what the --smv-word-level regression tests exercise.
static transition_systemt make_transition_system(
  const std::vector<symbol_exprt> &inputs,
  const std::vector<std::pair<irep_idt, exprt>> &wires)
{
  transition_systemt ts;

  symbolt module_symbol{"main", typet{ID_module}, ID_Verilog};
  module_symbol.base_name = "main";
  ts.symbol_table.add(module_symbol);
  ts.main_symbol = &ts.symbol_table.lookup_ref("main");

  auto declare = [&ts](const irep_idt &name, const typet &type)
  {
    symbolt symbol{name, type, ID_Verilog};
    symbol.base_name = name;
    symbol.module = "main";
    ts.symbol_table.add(symbol);
  };

  for(auto &input : inputs)
    declare(input.get_identifier(), input.type());

  exprt::operandst invar_conjuncts;

  for(auto &wire : wires)
  {
    const irep_idt &name = wire.first;
    const exprt &value = wire.second;

    declare(name, value.type());

    invar_conjuncts.push_back(
      equal_exprt{symbol_exprt{name, value.type()}, value});
  }

  ts.trans_expr = transt{
    ID_trans,
    conjunction(invar_conjuncts),
    true_exprt{},
    true_exprt{},
    typet{}};

  return ts;
}

/// Render the SMV word-level output and return only the INVAR lines, so
/// that the tests do not depend on the surrounding boilerplate (MODULE
/// header, VAR declaration order, etc.).
static std::vector<std::string> invar_lines(
  const std::vector<symbol_exprt> &inputs,
  const std::vector<std::pair<irep_idt, exprt>> &wires)
{
  auto ts = make_transition_system(inputs, wires);
  ebmc_propertiest properties;
  std::ostringstream out;
  output_smv_word_level(ts, properties, out);

  std::vector<std::string> result;
  std::istringstream in{out.str()};
  for(std::string line; std::getline(in, line);)
  {
    if(line.compare(0, 6, "INVAR ") == 0)
      result.push_back(line.substr(6));
  }
  return result;
}

SCENARIO("SMV word-level output: bitwise operators")
{
  auto u8 = unsignedbv_typet{8};
  auto a = symbol_exprt{"a", u8};
  auto b = symbol_exprt{"b", u8};

  GIVEN("the bitwise Verilog operators")
  {
    auto lines = invar_lines(
      {a, b},
      {{"w_and", bitand_exprt{a, b}},
       {"w_or", bitor_exprt{a, b}},
       {"w_xor", bitxor_exprt{a, b}},
       {"w_xnor", bitnot_exprt{bitxor_exprt{a, b}}},
       {"w_not", bitnot_exprt{a}}});

    THEN("they are printed using SMV word-level syntax")
    {
      REQUIRE(lines.size() == 5);
      REQUIRE(lines[0] == "w_and = (a & b)");
      REQUIRE(lines[1] == "w_or = (a | b)");
      REQUIRE(lines[2] == "w_xor = (a xor b)");
      REQUIRE(lines[3] == "w_xnor = !(a xor b)");
      REQUIRE(lines[4] == "w_not = !a");
    }
  }
}

SCENARIO("SMV word-level output: arithmetic operators")
{
  auto u8 = unsignedbv_typet{8};
  auto a = symbol_exprt{"a", u8};
  auto b = symbol_exprt{"b", u8};

  GIVEN("the arithmetic Verilog operators")
  {
    auto lines = invar_lines(
      {a, b},
      {{"diff", minus_exprt{a, b}},
       {"neg", unary_minus_exprt{a}},
       {"prod", mult_exprt{a, b}}});

    THEN("they are printed using SMV word-level syntax")
    {
      REQUIRE(lines.size() == 3);
      REQUIRE(lines[0] == "diff = a - b");
      REQUIRE(lines[1] == "neg = -a");
      REQUIRE(lines[2] == "prod = a * b");
    }
  }
}

SCENARIO("SMV word-level output: relational operators")
{
  auto u8 = unsignedbv_typet{8};
  auto a = symbol_exprt{"a", u8};
  auto b = symbol_exprt{"b", u8};

  GIVEN("the relational Verilog operators")
  {
    auto lines = invar_lines(
      {a, b},
      {{"w_lt", binary_relation_exprt{a, ID_lt, b}},
       {"w_gt", binary_relation_exprt{a, ID_gt, b}},
       {"w_le", binary_relation_exprt{a, ID_le, b}},
       {"w_ge", binary_relation_exprt{a, ID_ge, b}},
       {"w_ne", notequal_exprt{a, b}}});

    THEN("they are printed using SMV word-level syntax")
    {
      REQUIRE(lines.size() == 5);
      REQUIRE(lines[0] == "w_lt = (a < b)");
      REQUIRE(lines[1] == "w_gt = (a > b)");
      REQUIRE(lines[2] == "w_le = (a <= b)");
      REQUIRE(lines[3] == "w_ge = (a >= b)");
      REQUIRE(lines[4] == "w_ne = (a != b)");
    }
  }
}

SCENARIO("SMV word-level output: conditional operator")
{
  auto u8 = unsignedbv_typet{8};
  auto a = symbol_exprt{"a", u8};
  auto b = symbol_exprt{"b", u8};
  auto sel = symbol_exprt{"sel", bool_typet{}};

  GIVEN("a ?: expression")
  {
    auto lines = invar_lines({sel, a, b}, {{"mux", if_exprt{sel, a, b}}});

    THEN("it is printed using the SMV word-level conditional")
    {
      REQUIRE(lines.size() == 1);
      REQUIRE(lines[0] == "mux = (sel?a:b)");
    }
  }
}

SCENARIO("SMV word-level output: replication is concatenation")
{
  auto u4 = unsignedbv_typet{4};
  auto a = symbol_exprt{"a", u4};

  GIVEN("a two-fold and a three-fold replication of a")
  {
    auto lines = invar_lines(
      {a},
      {{"rep", concatenation_exprt{{a, a}, unsignedbv_typet{8}}},
       {"rep3", concatenation_exprt{{a, a, a}, unsignedbv_typet{12}}}});

    THEN("they are printed as SMV concatenation")
    {
      REQUIRE(lines.size() == 2);
      REQUIRE(lines[0] == "rep = a :: a");
      REQUIRE(lines[1] == "rep3 = a :: a :: a");
    }
  }
}
