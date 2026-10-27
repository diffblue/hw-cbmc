/*******************************************************************\

Module: Verilog Constant Folding Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <testing-utils/use_catch.h>
#include <verilog/verilog_constant_folding.h>
#include <verilog/verilog_types.h>

/// helper: build a four-valued 4-bit unsigned constant from a bit string,
/// which may contain x and z
static constant_exprt l4(const std::string &bits)
{
  PRECONDITION(bits.size() == 4);
  return constant_exprt{bits, verilog_unsignedbv_typet{4}};
}

/// helper: build a four-valued 4-bit signed constant from a bit string
static constant_exprt sl4(const std::string &bits)
{
  PRECONDITION(bits.size() == 4);
  return constant_exprt{bits, verilog_signedbv_typet{4}};
}

/// helper: build a four-valued 1-bit unsigned constant
static constant_exprt l1(const std::string &bit)
{
  PRECONDITION(bit.size() == 1);
  return constant_exprt{bit, verilog_unsignedbv_typet{1}};
}

/// helper: a four-valued relational expression; the result type is
/// a 1-bit four-valued vector, not bool
static binary_exprt l4_relation(
  const irep_idt &id,
  const constant_exprt &lhs,
  const constant_exprt &rhs)
{
  return binary_exprt{lhs, id, rhs, verilog_unsignedbv_typet{1}};
}

static mp_integer as_integer(const exprt &expr)
{
  REQUIRE(expr.is_constant());
  return numeric_cast_v<mp_integer>(to_constant_expr(expr));
}

SCENARIO("verilog_constant_folding folds two-valued expressions")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  GIVEN("1 + 2 as 32-bit signed")
  {
    auto type = signedbv_typet{32};
    plus_exprt expr{from_integer(1, type), from_integer(2, type)};

    THEN("the result is the constant 3 with the same type")
    {
      auto result = verilog_constant_folding(expr, ns);
      REQUIRE(as_integer(result) == 3);
      REQUIRE(result.type() == type);
    }
  }

  GIVEN("a two-valued relation")
  {
    auto type = unsignedbv_typet{8};
    binary_relation_exprt expr{
      from_integer(3, type), ID_lt, from_integer(4, type)};

    THEN("the result is true")
    {
      REQUIRE(verilog_constant_folding(expr, ns) == true_exprt{});
    }
  }
}

SCENARIO("verilog_constant_folding lifts four-valued constants")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  GIVEN("a four-valued constant")
  {
    THEN("the constant is returned unchanged")
    {
      REQUIRE(verilog_constant_folding(l4("x0z1"), ns) == l4("x0z1"));
      REQUIRE(verilog_constant_folding(l4("0101"), ns) == l4("0101"));
    }
  }

  GIVEN("four-valued arithmetic without x or z")
  {
    THEN("the result is a four-valued constant")
    {
      auto result =
        verilog_constant_folding(plus_exprt{l4("0011"), l4("0001")}, ns);
      REQUIRE(result == l4("0100"));
      REQUIRE(result.type() == verilog_unsignedbv_typet{4});

      REQUIRE(
        verilog_constant_folding(mult_exprt{l4("0011"), l4("0010")}, ns) ==
        l4("0110"));
    }
  }

  GIVEN("four-valued arithmetic with x or z")
  {
    THEN("the result is all x (1800-2017 11.4.3)")
    {
      REQUIRE(
        verilog_constant_folding(plus_exprt{l4("00x1"), l4("0001")}, ns) ==
        l4("xxxx"));
      REQUIRE(
        verilog_constant_folding(unary_minus_exprt{l4("000z")}, ns) ==
        l4("xxxx"));
    }
  }

  GIVEN("four-valued bit-wise operators (1800-2017 11.4.8)")
  {
    REQUIRE(
      verilog_constant_folding(bitand_exprt{l4("x0z1"), l4("1111")}, ns) ==
      l4("x0x1"));
    REQUIRE(
      verilog_constant_folding(bitand_exprt{l4("x0z1"), l4("0000")}, ns) ==
      l4("0000"));
    REQUIRE(
      verilog_constant_folding(bitor_exprt{l4("x0z1"), l4("0000")}, ns) ==
      l4("x0x1"));
    REQUIRE(
      verilog_constant_folding(bitor_exprt{l4("x0z1"), l4("1111")}, ns) ==
      l4("1111"));
    REQUIRE(
      verilog_constant_folding(bitnot_exprt{l4("x0z1")}, ns) == l4("x1x0"));
  }

  GIVEN("a signed four-valued expression")
  {
    THEN("the result has the signed four-valued type")
    {
      auto result =
        verilog_constant_folding(unary_minus_exprt{sl4("0001")}, ns);
      REQUIRE(result == sl4("1111"));
      REQUIRE(result.type() == verilog_signedbv_typet{4});
    }
  }

  GIVEN("a four-valued relation with a 1-bit four-valued result")
  {
    REQUIRE(
      verilog_constant_folding(
        l4_relation(ID_lt, l4("0011"), l4("0100")), ns) == l1("1"));
    REQUIRE(
      verilog_constant_folding(
        l4_relation(ID_gt, l4("0011"), l4("0100")), ns) == l1("0"));
    REQUIRE(
      verilog_constant_folding(
        l4_relation(ID_verilog_logical_equality, l4("00x1"), l4("0001")), ns) ==
      l1("x"));
  }

  GIVEN("a four-valued expression with a source location")
  {
    plus_exprt expr{l4("0011"), l4("0001")};
    source_locationt location;
    location.set_file("test.sv");
    location.set_line(42);
    expr.add_source_location() = location;

    THEN("the source location survives constant folding")
    {
      auto result = verilog_constant_folding(expr, ns);
      REQUIRE(result == l4("0100"));
      REQUIRE(result.source_location().get_file() == "test.sv");
      REQUIRE(result.source_location().get_line() == "42");
    }
  }
}

SCENARIO("verilog_constant_folding on non-constant expressions")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  GIVEN("a symbol plus a constant")
  {
    // Symbols have an elaborated, two-valued type at this point.
    auto type = unsignedbv_typet{8};
    symbol_exprt a{"a", type};
    plus_exprt expr{
      a, plus_exprt{from_integer(1, type), from_integer(2, type)}};

    THEN("the outer expression is not folded, but the inner one is")
    {
      auto result = verilog_constant_folding(expr, ns);
      REQUIRE(result.id() == ID_plus);
      REQUIRE(to_plus_expr(result).op0() == a);
      REQUIRE(as_integer(to_plus_expr(result).op1()) == 3);
    }
  }
}
