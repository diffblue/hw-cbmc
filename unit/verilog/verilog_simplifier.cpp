/*******************************************************************\

Module: Verilog Simplifier Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <testing-utils/use_catch.h>
#include <verilog/aval_bval_encoding.h>
#include <verilog/verilog_lowering.h>
#include <verilog/verilog_simplifier.h>
#include <verilog/verilog_types.h>

/// helper: build an 8-bit unsigned constant from a bit string
static constant_exprt u8(const std::string &bits)
{
  PRECONDITION(bits.size() == 8);
  return from_integer(string2integer(bits, 2), unsignedbv_typet{8});
}

/// helper: build a four-valued 4-bit unsigned constant from a bit string,
/// which may contain x and z
static constant_exprt l4(const std::string &bits)
{
  PRECONDITION(bits.size() == 4);
  return constant_exprt{bits, verilog_unsignedbv_typet{4}};
}

/// helper: build a four-valued 1-bit unsigned constant
static constant_exprt l1(const std::string &bit)
{
  PRECONDITION(bit.size() == 1);
  return constant_exprt{bit, verilog_unsignedbv_typet{1}};
}

/// helper: the aval/bval encoding of a four-valued constant, which is
/// what the simplifier produces for four-valued expressions
static constant_exprt encoded(const constant_exprt &expr)
{
  return lower_to_aval_bval(expr);
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

/// helper: lower and then simplify, as elaborate_constant_expression does
static exprt lower_and_simplify(exprt expr, const namespacet &ns)
{
  return verilog_simplifier(verilog_lowering(std::move(expr)), ns);
}

static mp_integer as_integer(const exprt &expr)
{
  REQUIRE(expr.is_constant());
  return numeric_cast_v<mp_integer>(to_constant_expr(expr));
}

SCENARIO("verilog_simplifier folds arithmetic")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  GIVEN("1 + 2 as 32-bit signed")
  {
    auto type = signedbv_typet{32};
    plus_exprt expr{from_integer(1, type), from_integer(2, type)};

    THEN("the result is the constant 3")
    {
      auto result = verilog_simplifier(expr, ns);
      REQUIRE(as_integer(result) == 3);
      REQUIRE(result.type() == type);
    }
  }

  GIVEN("a nested constant expression (1 + 2) * 4")
  {
    auto type = unsignedbv_typet{8};
    mult_exprt expr{
      plus_exprt{from_integer(1, type), from_integer(2, type)},
      from_integer(4, type)};

    THEN("the result is the constant 12")
    {
      REQUIRE(as_integer(verilog_simplifier(expr, ns)) == 12);
    }
  }

  GIVEN("the remaining arithmetic operators on 8-bit unsigned")
  {
    auto type = unsignedbv_typet{8};
    auto c = [&](int v) { return from_integer(v, type); };

    REQUIRE(as_integer(verilog_simplifier(minus_exprt{c(7), c(3)}, ns)) == 4);
    REQUIRE(as_integer(verilog_simplifier(div_exprt{c(7), c(2)}, ns)) == 3);
    REQUIRE(as_integer(verilog_simplifier(mod_exprt{c(7), c(2)}, ns)) == 1);
    // wrap-around
    REQUIRE(as_integer(verilog_simplifier(plus_exprt{c(255), c(1)}, ns)) == 0);
    REQUIRE(as_integer(verilog_simplifier(unary_minus_exprt{c(1)}, ns)) == 255);
  }

  GIVEN("signed arithmetic")
  {
    auto type = signedbv_typet{8};
    auto c = [&](int v) { return from_integer(v, type); };

    REQUIRE(as_integer(verilog_simplifier(unary_minus_exprt{c(1)}, ns)) == -1);
    REQUIRE(as_integer(verilog_simplifier(div_exprt{c(-7), c(2)}, ns)) == -3);
    REQUIRE(as_integer(verilog_simplifier(mod_exprt{c(-7), c(2)}, ns)) == -1);
  }
}

SCENARIO("verilog_simplifier folds relational operators")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  auto type = unsignedbv_typet{8};
  auto c = [&](int v) { return from_integer(v, type); };
  auto rel = [&](const irep_idt &id, int lhs, int rhs) {
    return verilog_simplifier(binary_relation_exprt{c(lhs), id, c(rhs)}, ns);
  };

  GIVEN("equality and inequality")
  {
    REQUIRE(rel(ID_equal, 3, 3) == true_exprt{});
    REQUIRE(rel(ID_equal, 3, 4) == false_exprt{});
    REQUIRE(rel(ID_notequal, 3, 3) == false_exprt{});
    REQUIRE(rel(ID_notequal, 3, 4) == true_exprt{});
  }

  GIVEN("ordering")
  {
    REQUIRE(rel(ID_lt, 3, 4) == true_exprt{});
    REQUIRE(rel(ID_lt, 4, 3) == false_exprt{});
    REQUIRE(rel(ID_lt, 3, 3) == false_exprt{});
    REQUIRE(rel(ID_le, 3, 3) == true_exprt{});
    REQUIRE(rel(ID_le, 4, 3) == false_exprt{});
    REQUIRE(rel(ID_gt, 4, 3) == true_exprt{});
    REQUIRE(rel(ID_gt, 3, 3) == false_exprt{});
    REQUIRE(rel(ID_ge, 3, 3) == true_exprt{});
    REQUIRE(rel(ID_ge, 3, 4) == false_exprt{});
  }

  GIVEN("signed ordering")
  {
    auto stype = signedbv_typet{8};
    REQUIRE(
      verilog_simplifier(
        binary_relation_exprt{
          from_integer(-1, stype), ID_lt, from_integer(1, stype)},
        ns) == true_exprt{});
    // the same bit pattern is 255 when unsigned
    REQUIRE(rel(ID_lt, 255, 1) == false_exprt{});
  }
}

SCENARIO("verilog_simplifier folds bit-wise operators")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  GIVEN("binary bit-wise operators")
  {
    REQUIRE(
      as_integer(verilog_simplifier(
        bitand_exprt{u8("00110101"), u8("00001111")}, ns)) == 0b00000101);
    REQUIRE(
      as_integer(verilog_simplifier(
        bitor_exprt{u8("00110101"), u8("00001111")}, ns)) == 0b00111111);
    REQUIRE(
      as_integer(verilog_simplifier(
        bitxor_exprt{u8("00110101"), u8("00001111")}, ns)) == 0b00111010);
  }

  GIVEN("bit-wise negation")
  {
    REQUIRE(
      as_integer(verilog_simplifier(bitnot_exprt{u8("00110101")}, ns)) ==
      0b11001010);
  }

  GIVEN("shifts")
  {
    auto dist = from_integer(2, unsignedbv_typet{32});
    REQUIRE(
      as_integer(verilog_simplifier(shl_exprt{u8("00110101"), dist}, ns)) ==
      0b11010100);
    REQUIRE(
      as_integer(verilog_simplifier(lshr_exprt{u8("00110101"), dist}, ns)) ==
      0b00001101);
    REQUIRE(
      as_integer(verilog_simplifier(
        ashr_exprt{from_integer(-128, signedbv_typet{8}), dist}, ns)) == -32);
  }
}

SCENARIO("verilog_simplifier folds four-valued arithmetic")
{
  // Four-valued expressions reach the simplifier after verilog_lowering
  // has turned them into aval/bval-encoded two-valued expressions.
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  GIVEN("operands without x or z")
  {
    REQUIRE(
      lower_and_simplify(plus_exprt{l4("0011"), l4("0001")}, ns) ==
      encoded(l4("0100")));
    REQUIRE(
      lower_and_simplify(minus_exprt{l4("0011"), l4("0001")}, ns) ==
      encoded(l4("0010")));
    REQUIRE(
      lower_and_simplify(mult_exprt{l4("0011"), l4("0010")}, ns) ==
      encoded(l4("0110")));
    REQUIRE(
      lower_and_simplify(div_exprt{l4("0110"), l4("0010")}, ns) ==
      encoded(l4("0011")));
    REQUIRE(
      lower_and_simplify(mod_exprt{l4("0111"), l4("0010")}, ns) ==
      encoded(l4("0001")));
    REQUIRE(
      lower_and_simplify(unary_minus_exprt{l4("0001")}, ns) ==
      encoded(l4("1111")));
  }

  GIVEN("operands with x or z")
  {
    // IEEE 1800-2017 11.4.3: if any operand bit is x or z, the result is
    // all x
    REQUIRE(
      lower_and_simplify(plus_exprt{l4("00x1"), l4("0001")}, ns) ==
      encoded(l4("xxxx")));
    REQUIRE(
      lower_and_simplify(mult_exprt{l4("0011"), l4("00z0")}, ns) ==
      encoded(l4("xxxx")));
    REQUIRE(
      lower_and_simplify(unary_minus_exprt{l4("000x")}, ns) ==
      encoded(l4("xxxx")));
  }
}

SCENARIO("verilog_simplifier folds four-valued relational operators")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  GIVEN("logical equality and inequality")
  {
    REQUIRE(
      lower_and_simplify(
        l4_relation(ID_verilog_logical_equality, l4("0011"), l4("0011")), ns) ==
      encoded(l1("1")));
    REQUIRE(
      lower_and_simplify(
        l4_relation(ID_verilog_logical_equality, l4("0011"), l4("0001")), ns) ==
      encoded(l1("0")));
    REQUIRE(
      lower_and_simplify(
        l4_relation(ID_verilog_logical_inequality, l4("0011"), l4("0001")),
        ns) == encoded(l1("1")));

    // IEEE 1800-2017 11.4.5: x if either operand contains x or z
    REQUIRE(
      lower_and_simplify(
        l4_relation(ID_verilog_logical_equality, l4("00x1"), l4("0001")), ns) ==
      encoded(l1("x")));
    REQUIRE(
      lower_and_simplify(
        l4_relation(ID_verilog_logical_inequality, l4("00z1"), l4("0001")),
        ns) == encoded(l1("x")));
  }

  GIVEN("ordering")
  {
    REQUIRE(
      lower_and_simplify(l4_relation(ID_lt, l4("0011"), l4("0100")), ns) ==
      encoded(l1("1")));
    REQUIRE(
      lower_and_simplify(l4_relation(ID_lt, l4("0100"), l4("0011")), ns) ==
      encoded(l1("0")));
    REQUIRE(
      lower_and_simplify(l4_relation(ID_le, l4("0011"), l4("0011")), ns) ==
      encoded(l1("1")));
    REQUIRE(
      lower_and_simplify(l4_relation(ID_ge, l4("0011"), l4("0011")), ns) ==
      encoded(l1("1")));
    REQUIRE(
      lower_and_simplify(l4_relation(ID_ge, l4("0011"), l4("0100")), ns) ==
      encoded(l1("0")));

    // IEEE 1800-2017 11.4.4: x if either operand contains x or z
    REQUIRE(
      lower_and_simplify(l4_relation(ID_lt, l4("00x1"), l4("0100")), ns) ==
      encoded(l1("x")));
  }
}

SCENARIO("verilog_simplifier folds four-valued bit-wise operators")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  GIVEN("operands without x or z")
  {
    REQUIRE(
      lower_and_simplify(bitand_exprt{l4("0011"), l4("0101")}, ns) ==
      encoded(l4("0001")));
    REQUIRE(
      lower_and_simplify(bitor_exprt{l4("0011"), l4("0101")}, ns) ==
      encoded(l4("0111")));
    REQUIRE(
      lower_and_simplify(bitxor_exprt{l4("0011"), l4("0101")}, ns) ==
      encoded(l4("0110")));
    REQUIRE(
      lower_and_simplify(bitnot_exprt{l4("0011")}, ns) == encoded(l4("1100")));
  }

  GIVEN("operands with x or z, IEEE 1800-2017 11.4.8")
  {
    // 0 & x = 0, 1 & x = x, z behaves like x
    REQUIRE(
      lower_and_simplify(bitand_exprt{l4("x0z1"), l4("0000")}, ns) ==
      encoded(l4("0000")));
    REQUIRE(
      lower_and_simplify(bitand_exprt{l4("x0z1"), l4("1111")}, ns) ==
      encoded(l4("x0x1")));

    // 1 | x = 1, 0 | x = x
    REQUIRE(
      lower_and_simplify(bitor_exprt{l4("x0z1"), l4("1111")}, ns) ==
      encoded(l4("1111")));
    REQUIRE(
      lower_and_simplify(bitor_exprt{l4("x0z1"), l4("0000")}, ns) ==
      encoded(l4("x0x1")));

    // any x or z input gives x
    REQUIRE(
      lower_and_simplify(bitxor_exprt{l4("x0z1"), l4("0101")}, ns) ==
      encoded(l4("x1x0")));
    REQUIRE(
      lower_and_simplify(bitnot_exprt{l4("x0z1")}, ns) == encoded(l4("x1x0")));
  }

  GIVEN("shifts")
  {
    auto dist = from_integer(1, unsignedbv_typet{32});
    REQUIRE(
      lower_and_simplify(shl_exprt{l4("0011"), dist}, ns) ==
      encoded(l4("0110")));
    REQUIRE(
      lower_and_simplify(lshr_exprt{l4("0011"), dist}, ns) ==
      encoded(l4("0001")));
    // x and z bits are shifted along unchanged
    REQUIRE(
      lower_and_simplify(shl_exprt{l4("0x1z"), dist}, ns) ==
      encoded(l4("x1z0")));
  }
}

SCENARIO("verilog_simplifier gives up on non-constant operands")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  GIVEN("a + (1 + 2) where a is a symbol")
  {
    auto type = unsignedbv_typet{8};
    symbol_exprt a{"a", type};
    plus_exprt expr{
      a, plus_exprt{from_integer(1, type), from_integer(2, type)}};

    THEN("the outer expression is not folded, but the inner one is")
    {
      auto result = verilog_simplifier(expr, ns);
      REQUIRE(result.id() == ID_plus);
      REQUIRE(result.operands().size() == 2);
      REQUIRE(to_plus_expr(result).op0() == a);
      REQUIRE(as_integer(to_plus_expr(result).op1()) == 3);
    }
  }

  GIVEN("|a where a is a symbol")
  {
    symbol_exprt a{"a", unsignedbv_typet{8}};
    reduction_or_exprt expr{a};

    THEN("the reduction operator is left alone")
    {
      auto result = verilog_simplifier(expr, ns);
      REQUIRE(result == expr);
    }
  }
}

SCENARIO("verilog_simplifier folds reduction operators")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  GIVEN("reduction or")
  {
    REQUIRE(
      verilog_simplifier(reduction_or_exprt{u8("00000100")}, ns) ==
      true_exprt{});
    REQUIRE(
      verilog_simplifier(reduction_or_exprt{u8("00000000")}, ns) ==
      false_exprt{});
  }

  GIVEN("reduction nor")
  {
    REQUIRE(
      verilog_simplifier(reduction_nor_exprt{u8("00000100")}, ns) ==
      false_exprt{});
    REQUIRE(
      verilog_simplifier(reduction_nor_exprt{u8("00000000")}, ns) ==
      true_exprt{});
  }

  GIVEN("reduction and on unsigned")
  {
    REQUIRE(
      verilog_simplifier(reduction_and_exprt{u8("11111111")}, ns) ==
      true_exprt{});
    REQUIRE(
      verilog_simplifier(reduction_and_exprt{u8("11111011")}, ns) ==
      false_exprt{});
  }

  GIVEN("reduction and on signed")
  {
    auto type = signedbv_typet{8};
    REQUIRE(
      verilog_simplifier(reduction_and_exprt{from_integer(-1, type)}, ns) ==
      true_exprt{});
    REQUIRE(
      verilog_simplifier(reduction_and_exprt{from_integer(127, type)}, ns) ==
      false_exprt{});
  }

  GIVEN("reduction and on bool")
  {
    REQUIRE(
      verilog_simplifier(reduction_and_exprt{true_exprt{}}, ns) ==
      true_exprt{});
    REQUIRE(
      verilog_simplifier(reduction_and_exprt{false_exprt{}}, ns) ==
      false_exprt{});
  }

  GIVEN("reduction nand")
  {
    REQUIRE(
      verilog_simplifier(reduction_nand_exprt{u8("11111111")}, ns) ==
      false_exprt{});
    REQUIRE(
      verilog_simplifier(reduction_nand_exprt{u8("11111011")}, ns) ==
      true_exprt{});
  }

  GIVEN("reduction xor")
  {
    // odd number of ones
    REQUIRE(
      verilog_simplifier(reduction_xor_exprt{u8("00000111")}, ns) ==
      true_exprt{});
    // even number of ones
    REQUIRE(
      verilog_simplifier(reduction_xor_exprt{u8("00000011")}, ns) ==
      false_exprt{});
    REQUIRE(
      verilog_simplifier(reduction_xor_exprt{u8("00000000")}, ns) ==
      false_exprt{});
  }

  GIVEN("reduction xnor")
  {
    REQUIRE(
      verilog_simplifier(reduction_xnor_exprt{u8("00000111")}, ns) ==
      false_exprt{});
    REQUIRE(
      verilog_simplifier(reduction_xnor_exprt{u8("00000011")}, ns) ==
      true_exprt{});
  }

  GIVEN("reduction xor on a four-valued operand")
  {
    // x and z bits do not count as ones
    REQUIRE(
      verilog_simplifier(reduction_xor_exprt{l4("1x0z")}, ns) == true_exprt{});
    REQUIRE(
      verilog_simplifier(reduction_xor_exprt{l4("1xz1")}, ns) == false_exprt{});
  }
}

SCENARIO("verilog_simplifier folds replication")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  GIVEN("{3{2'b10}}")
  {
    replication_exprt expr{
      from_integer(3, integer_typet{}),
      from_integer(0b10, unsignedbv_typet{2}),
      unsignedbv_typet{6}};

    THEN("the result is 6'b101010")
    {
      auto result = verilog_simplifier(expr, ns);
      REQUIRE(as_integer(result) == 0b101010);
      REQUIRE(result.type() == unsignedbv_typet{6});
    }
  }

  GIVEN("{1{8'hA5}}")
  {
    replication_exprt expr{
      from_integer(1, integer_typet{}), u8("10100101"), unsignedbv_typet{8}};

    THEN("the result is the operand")
    {
      REQUIRE(as_integer(verilog_simplifier(expr, ns)) == 0xA5);
    }
  }
}

SCENARIO("verilog_simplifier folds $onehot and $onehot0")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  GIVEN("$onehot on two-valued operands")
  {
    REQUIRE(
      verilog_simplifier(onehot_exprt{u8("00000100")}, ns) == true_exprt{});
    REQUIRE(
      verilog_simplifier(onehot_exprt{u8("00000110")}, ns) == false_exprt{});
    REQUIRE(
      verilog_simplifier(onehot_exprt{u8("00000000")}, ns) == false_exprt{});
  }

  GIVEN("$onehot0 on two-valued operands")
  {
    REQUIRE(
      verilog_simplifier(onehot0_exprt{u8("00000000")}, ns) == true_exprt{});
    REQUIRE(
      verilog_simplifier(onehot0_exprt{u8("10000000")}, ns) == true_exprt{});
    REQUIRE(
      verilog_simplifier(onehot0_exprt{u8("10000001")}, ns) == false_exprt{});
  }

  GIVEN("$onehot on four-valued operands")
  {
    // x and z bits do not count as ones
    REQUIRE(verilog_simplifier(onehot_exprt{l4("01x0")}, ns) == true_exprt{});
    REQUIRE(verilog_simplifier(onehot_exprt{l4("xxzz")}, ns) == false_exprt{});
    REQUIRE(verilog_simplifier(onehot_exprt{l4("1x1z")}, ns) == false_exprt{});
  }

  GIVEN("$onehot0 on four-valued operands")
  {
    REQUIRE(verilog_simplifier(onehot0_exprt{l4("xxzz")}, ns) == true_exprt{});
    REQUIRE(verilog_simplifier(onehot0_exprt{l4("1xz0")}, ns) == true_exprt{});
    REQUIRE(verilog_simplifier(onehot0_exprt{l4("1x1z")}, ns) == false_exprt{});
  }

  GIVEN("$onehot on a symbol")
  {
    onehot_exprt expr{symbol_exprt{"a", unsignedbv_typet{8}}};

    THEN("the expression is left alone")
    {
      REQUIRE(verilog_simplifier(expr, ns) == expr);
    }
  }
}

SCENARIO("verilog_simplifier preserves annotations")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  GIVEN("an expression with Verilog type annotation")
  {
    auto type = verilog_int_typet{}.lower();
    REQUIRE(type.get(ID_C_verilog_type) == ID_verilog_int);
    plus_exprt expr{from_integer(1, type), from_integer(2, type)};

    THEN("the annotation survives simplification")
    {
      auto result = verilog_simplifier(expr, ns);
      REQUIRE(as_integer(result) == 3);
      REQUIRE(result.type().get(ID_C_verilog_type) == ID_verilog_int);
    }
  }

  GIVEN("an expression with a type identifier annotation")
  {
    auto type = unsignedbv_typet{8};
    type.set(ID_C_identifier, "my_type");
    plus_exprt expr{from_integer(1, type), from_integer(2, type)};

    THEN("the identifier survives simplification")
    {
      auto result = verilog_simplifier(expr, ns);
      REQUIRE(as_integer(result) == 3);
      REQUIRE(result.type().get(ID_C_identifier) == "my_type");
    }
  }

  GIVEN("an expression with a source location")
  {
    auto type = unsignedbv_typet{8};
    plus_exprt expr{from_integer(1, type), from_integer(2, type)};
    source_locationt location;
    location.set_file("test.sv");
    location.set_line(42);
    expr.add_source_location() = location;

    THEN("the source location survives simplification")
    {
      auto result = verilog_simplifier(expr, ns);
      REQUIRE(as_integer(result) == 3);
      REQUIRE(result.source_location().get_file() == "test.sv");
      REQUIRE(result.source_location().get_line() == "42");
    }
  }
}
