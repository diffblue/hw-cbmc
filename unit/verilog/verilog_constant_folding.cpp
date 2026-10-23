/*******************************************************************\

Module: Verilog Constant Folding Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/ieee_float.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <testing-utils/use_catch.h>
#include <verilog/aval_bval_encoding.h>
#include <verilog/verilog_constant_folding.h>
#include <verilog/verilog_expr.h>
#include <verilog/verilog_lowering.h>
#include <verilog/verilog_simplifier.h>
#include <verilog/verilog_types.h>

// Helpers to build Verilog constants

/// An empty namespace for the folder; the test expressions are
/// self-contained constants and contain no symbols.
static const symbol_tablet constant_fold_symbol_table;
static const namespacet constant_fold_ns{constant_fold_symbol_table};

/// Fold a type-checked Verilog expression. A thin wrapper around
/// verilog_constant_folding that supplies the (empty) namespace.
static exprt verilog_constant_fold(exprt expr)
{
  return verilog_constant_folding(std::move(expr), constant_fold_ns);
}


/// two-valued unsigned
static constant_exprt u(std::size_t width, const mp_integer &value)
{
  return from_integer(value, unsignedbv_typet{width});
}

/// two-valued signed
static constant_exprt s(std::size_t width, const mp_integer &value)
{
  return from_integer(value, signedbv_typet{width});
}

/// four-valued unsigned, digits most-significant first
static constant_exprt lu(const std::string &digits)
{
  return constant_exprt{digits, verilog_unsignedbv_typet{digits.size()}};
}

/// four-valued signed, digits most-significant first
static constant_exprt ls(const std::string &digits)
{
  return constant_exprt{digits, verilog_signedbv_typet{digits.size()}};
}

static constant_exprt real(double value)
{
  ieee_floatt f{
    ieee_float_spect::double_precision(),
    ieee_floatt::rounding_modet::ROUND_TO_EVEN};
  f.from_double(value);
  return constant_exprt{integer2bvrep(f.pack(), 64), verilog_real_typet{}};
}

static double to_double(const exprt &expr)
{
  REQUIRE(expr.is_constant());
  REQUIRE(expr.type().id() == ID_verilog_real);
  ieee_floatt f{
    ieee_float_spect::double_precision(),
    ieee_floatt::rounding_modet::ROUND_TO_EVEN};
  f.unpack(bvrep2integer(to_constant_expr(expr).get_value(), 64, false));
  return f.to_double();
}

/// The digits of a folded integral constant, most-significant first
static std::string digits(const exprt &expr)
{
  REQUIRE(expr.is_constant());
  auto &constant = to_constant_expr(expr);
  auto &type = expr.type();
  if(type.id() == ID_verilog_unsignedbv || type.id() == ID_verilog_signedbv)
    return id2string(constant.get_value());
  else if(type.id() == ID_bool)
    return constant.is_true() ? "1" : "0";
  else
  {
    auto width = to_bitvector_type(type).get_width();
    auto value = bvrep2integer(constant.get_value(), width, false);
    std::string result;
    for(std::size_t i = 0; i < width; i++)
    {
      result = ((value % 2) == 1 ? "1" : "0") + result;
      value /= 2;
    }
    return result;
  }
}

static mp_integer value_of(const exprt &expr)
{
  REQUIRE(expr.is_constant());
  if(expr.type().id() == ID_bool)
    return expr.is_true() ? 1 : 0;
  return numeric_cast_v<mp_integer>(to_constant_expr(expr));
}

static const auto one_bit = verilog_unsignedbv_typet{1};
static const auto u4 = unsignedbv_typet{4};
static const auto s4 = signedbv_typet{4};
static const auto lu4 = verilog_unsignedbv_typet{4};
static const auto ls4 = verilog_signedbv_typet{4};

// Some of the expression classes have no constructor that takes a type;
// these helpers build the expressions generically.
static binary_exprt
bin(const exprt &a, const irep_idt &id, const exprt &b, const typet &type)
{
  return binary_exprt{a, id, b, type};
}

static exprt lnot(const exprt &a, const typet &type)
{
  return unary_exprt{ID_not, a, type};
}

static exprt land(const exprt &a, const exprt &b, const typet &type)
{
  return multi_ary_exprt{ID_and, {a, b}, type};
}

static exprt lor(const exprt &a, const exprt &b, const typet &type)
{
  return multi_ary_exprt{ID_or, {a, b}, type};
}

static exprt bit_select(const exprt &src, const exprt &index, const typet &type)
{
  return verilog_bit_select_exprt{src, index, type};
}

static exprt part_select(
  const exprt &src,
  const exprt &msb,
  const exprt &lsb,
  const typet &type)
{
  return verilog_non_indexed_part_select_exprt{src, msb, lsb, type};
}

static exprt indexed_part_select(
  const irep_idt &id,
  const exprt &src,
  const exprt &index,
  const exprt &width,
  const typet &type)
{
  return verilog_indexed_part_select_plus_or_minus_exprt{
    id, src, index, width, type};
}

SCENARIO("two-valued arithmetic")
{
  GIVEN("unsigned addition with wrap-around")
  {
    auto expr = plus_exprt{u(4, 9), u(4, 10), u4};
    REQUIRE(value_of(verilog_constant_fold(expr)) == 3);
  }

  GIVEN("signed addition")
  {
    auto expr = plus_exprt{s(4, -3), s(4, 2), s4};
    REQUIRE(value_of(verilog_constant_fold(expr)) == -1);
  }

  GIVEN("subtraction below zero wraps")
  {
    auto expr = minus_exprt{u(4, 1), u(4, 2)};
    REQUIRE(value_of(verilog_constant_fold(expr)) == 15);
  }

  GIVEN("multiplication")
  {
    auto expr = mult_exprt{s(8, -3), s(8, 7)};
    REQUIRE(value_of(verilog_constant_fold(expr)) == -21);
  }

  GIVEN("unary minus")
  {
    auto expr = unary_minus_exprt{s(8, 5)};
    REQUIRE(value_of(verilog_constant_fold(expr)) == -5);
    auto expr2 = unary_minus_exprt{u(4, 1)};
    REQUIRE(value_of(verilog_constant_fold(expr2)) == 15);
  }

  GIVEN("division truncates towards zero")
  {
    REQUIRE(
      value_of(verilog_constant_fold(div_exprt{s(8, -7), s(8, 2)})) == -3);
    REQUIRE(
      value_of(verilog_constant_fold(div_exprt{s(8, 7), s(8, -2)})) == -3);
    REQUIRE(value_of(verilog_constant_fold(div_exprt{u(8, 7), u(8, 2)})) == 3);
  }

  GIVEN("modulus takes the sign of the first operand")
  {
    REQUIRE(
      value_of(verilog_constant_fold(mod_exprt{s(8, -7), s(8, 2)})) == -1);
    REQUIRE(value_of(verilog_constant_fold(mod_exprt{s(8, 7), s(8, -2)})) == 1);
    REQUIRE(value_of(verilog_constant_fold(mod_exprt{u(8, 7), u(8, 2)})) == 1);
  }

  GIVEN("division by zero of a two-valued operand is not folded")
  {
    // The simplifier does not define division by zero for two-valued
    // operands, so the expression is returned with its operands folded.
    REQUIRE(!verilog_constant_fold(div_exprt{u(8, 7), u(8, 0)}).is_constant());
    REQUIRE(!verilog_constant_fold(mod_exprt{u(8, 7), u(8, 0)}).is_constant());
  }

  GIVEN("power, Table 11-4")
  {
    auto p = [](const constant_exprt &b, const constant_exprt &e) {
      return value_of(verilog_constant_fold(power_exprt{b, e}));
    };
    REQUIRE(p(s(8, 2), s(8, 3)) == 8);
    REQUIRE(p(s(8, 2), s(8, 0)) == 1);
    REQUIRE(p(s(8, 2), s(8, -1)) == 0);
    REQUIRE(p(s(8, -2), s(8, -1)) == 0);
    REQUIRE(p(s(8, 1), s(8, -5)) == 1);
    REQUIRE(p(s(8, 1), s(8, 5)) == 1);
    REQUIRE(p(s(8, -1), s(8, 3)) == -1);
    REQUIRE(p(s(8, -1), s(8, 4)) == 1);
    REQUIRE(p(s(8, -1), s(8, -3)) == -1);
    REQUIRE(p(s(8, -1), s(8, -4)) == 1);
    REQUIRE(p(s(8, 0), s(8, 0)) == 1);
    REQUIRE(p(s(8, 0), s(8, 3)) == 0);
    // 0 to a negative power is x, i.e. 0 for a two-valued type
    REQUIRE(p(s(8, 0), s(8, -1)) == 0);
    // unsigned base
    REQUIRE(p(u(8, 3), u(8, 4)) == 81);
    // wrap-around
    REQUIRE(p(u(8, 2), u(8, 9)) == 0);
    REQUIRE(p(u(8, 3), u(8, 5)) == 243);
    REQUIRE(p(u(8, 3), u(8, 6)) == (729 % 256));
  }

  GIVEN("a large exponent is folded without blowing up")
  {
    auto expr = power_exprt{u(8, 3), u(32, 1000000)};
    auto folded = verilog_constant_fold(expr);
    REQUIRE(folded.is_constant());
  }
}

SCENARIO("four-valued arithmetic")
{
  GIVEN("x in an operand makes the result all x")
  {
    auto expr = plus_exprt{lu("010x"), lu("0001"), lu4};
    REQUIRE(digits(verilog_constant_fold(expr)) == "xxxx");
    auto expr2 = mult_exprt{lu("0010"), lu("00z1")};
    REQUIRE(digits(verilog_constant_fold(expr2)) == "xxxx");
    auto expr3 = unary_minus_exprt{ls("0x00")};
    REQUIRE(digits(verilog_constant_fold(expr3)) == "xxxx");
  }

  GIVEN("four-valued operands without x/z fold like two-valued ones")
  {
    auto expr = plus_exprt{lu("1001"), lu("1010"), lu4};
    REQUIRE(digits(verilog_constant_fold(expr)) == "0011");
    REQUIRE(verilog_constant_fold(expr).type() == lu4);
    auto expr2 = minus_exprt{ls("1111"), ls("0001")};
    REQUIRE(digits(verilog_constant_fold(expr2)) == "1110");
  }

  GIVEN("division by zero yields x")
  {
    REQUIRE(
      digits(verilog_constant_fold(div_exprt{lu("0111"), lu("0000")})) ==
      "xxxx");
    REQUIRE(
      digits(verilog_constant_fold(mod_exprt{lu("0111"), lu("0000")})) ==
      "xxxx");
  }

  GIVEN("0 to a negative power yields x")
  {
    auto expr = power_exprt{ls("0000"), ls("1111")};
    REQUIRE(digits(verilog_constant_fold(expr)) == "xxxx");
  }
}

SCENARIO("real arithmetic")
{
  GIVEN("addition, subtraction, multiplication, division")
  {
    REQUIRE(
      to_double(verilog_constant_fold(
        plus_exprt{real(1.5), real(2.25), verilog_real_typet{}})) == 3.75);
    REQUIRE(
      to_double(verilog_constant_fold(minus_exprt{real(1.5), real(2.25)})) ==
      -0.75);
    REQUIRE(
      to_double(verilog_constant_fold(mult_exprt{real(1.5), real(2.0)})) ==
      3.0);
    REQUIRE(
      to_double(verilog_constant_fold(div_exprt{real(1.0), real(4.0)})) ==
      0.25);
    REQUIRE(
      to_double(verilog_constant_fold(unary_minus_exprt{real(1.5)})) == -1.5);
  }

  GIVEN("power")
  {
    REQUIRE(
      to_double(verilog_constant_fold(power_exprt{real(2.0), real(10.0)})) ==
      1024.0);
    REQUIRE(
      to_double(verilog_constant_fold(power_exprt{real(4.0), real(0.5)})) ==
      2.0);
  }

  GIVEN("division by zero gives infinity")
  {
    auto folded = verilog_constant_fold(div_exprt{real(1.0), real(0.0)});
    REQUIRE(std::isinf(to_double(folded)));
  }

  GIVEN("relations")
  {
    REQUIRE(
      value_of(verilog_constant_fold(
        binary_relation_exprt{real(1.5), ID_lt, real(2.0)})) == 1);
    REQUIRE(
      value_of(verilog_constant_fold(
        binary_relation_exprt{real(2.0), ID_lt, real(1.5)})) == 0);
    REQUIRE(
      value_of(verilog_constant_fold(
        binary_relation_exprt{real(2.0), ID_ge, real(2.0)})) == 1);
    REQUIRE(
      value_of(verilog_constant_fold(equal_exprt{real(2.0), real(2.0)})) == 1);
    REQUIRE(
      value_of(verilog_constant_fold(notequal_exprt{real(2.0), real(2.5)})) ==
      1);
  }
}

SCENARIO("bitwise operators, Tables 11-9 to 11-12")
{
  // all 16 digit pairs; z behaves like x
  const std::string digits_a =
    "0000"
    "1111"
    "xxxx"
    "zzzz";
  const std::string digits_b =
    "01xz"
    "01xz"
    "01xz"
    "01xz";

  GIVEN("&")
  {
    auto folded =
      verilog_constant_fold(bitand_exprt{lu(digits_a), lu(digits_b)});
    REQUIRE(
      digits(folded) ==
      "0000"
      "01xx"
      "0xxx"
      "0xxx");
  }

  GIVEN("|")
  {
    auto folded =
      verilog_constant_fold(bitor_exprt{lu(digits_a), lu(digits_b)});
    REQUIRE(
      digits(folded) ==
      "01xx"
      "1111"
      "x1xx"
      "x1xx");
  }

  GIVEN("^")
  {
    auto folded =
      verilog_constant_fold(bitxor_exprt{lu(digits_a), lu(digits_b)});
    REQUIRE(
      digits(folded) ==
      "01xx"
      "10xx"
      "xxxx"
      "xxxx");
  }

  GIVEN("~^")
  {
    auto folded =
      verilog_constant_fold(bitxnor_exprt{lu(digits_a), lu(digits_b)});
    REQUIRE(
      digits(folded) ==
      "10xx"
      "01xx"
      "xxxx"
      "xxxx");
  }

  GIVEN("~& and ~| of four-valued operands are not folded")
  {
    // The lowering has no aval/bval encoding for bitnand/bitnor, so
    // these are left unfolded for four-valued operands.
    REQUIRE(!verilog_constant_fold(bitnand_exprt{lu(digits_a), lu(digits_b)})
               .is_constant());
    REQUIRE(!verilog_constant_fold(bitnor_exprt{lu(digits_a), lu(digits_b)})
               .is_constant());
  }

  GIVEN("~")
  {
    auto folded = verilog_constant_fold(bitnot_exprt{lu("01xz")});
    REQUIRE(digits(folded) == "10xx");
  }

  GIVEN("two-valued operands")
  {
    REQUIRE(
      value_of(verilog_constant_fold(bitand_exprt{u(4, 12), u(4, 10)})) == 8);
    REQUIRE(
      value_of(verilog_constant_fold(bitor_exprt{u(4, 12), u(4, 10)})) == 14);
    REQUIRE(
      value_of(verilog_constant_fold(bitxor_exprt{u(4, 12), u(4, 10)})) == 6);
    REQUIRE(value_of(verilog_constant_fold(bitnot_exprt{u(4, 12)})) == 3);
    REQUIRE(value_of(verilog_constant_fold(bitnot_exprt{s(4, 0)})) == -1);
  }

  GIVEN("bitwise operators with more than two operands")
  {
    auto expr = multi_ary_exprt{ID_bitand, {u(4, 15), u(4, 7), u(4, 3)}, u4};
    REQUIRE(value_of(verilog_constant_fold(expr)) == 3);
  }
}

SCENARIO("reduction operators, Tables 11-13 to 11-15")
{
  auto red = [](const irep_idt &id, const constant_exprt &op)
  {
    auto type =
      is_four_valued(op.type()) ? typet{one_bit} : typet{bool_typet{}};
    return digits(verilog_constant_fold(unary_exprt{id, op, type}));
  };

  GIVEN("&")
  {
    REQUIRE(red(ID_reduction_and, lu("1111")) == "1");
    REQUIRE(red(ID_reduction_and, lu("1101")) == "0");
    REQUIRE(red(ID_reduction_and, lu("11x1")) == "x");
    REQUIRE(red(ID_reduction_and, lu("10x1")) == "0"); // 0 dominates
    REQUIRE(red(ID_reduction_and, lu("1z11")) == "x");
    REQUIRE(red(ID_reduction_nand, lu("1111")) == "0");
    REQUIRE(red(ID_reduction_nand, lu("10x1")) == "1");
    REQUIRE(red(ID_reduction_nand, lu("11x1")) == "x");
  }

  GIVEN("|")
  {
    REQUIRE(red(ID_reduction_or, lu("0000")) == "0");
    REQUIRE(red(ID_reduction_or, lu("0010")) == "1");
    REQUIRE(red(ID_reduction_or, lu("00x0")) == "x");
    REQUIRE(red(ID_reduction_or, lu("01x0")) == "1"); // 1 dominates
    REQUIRE(red(ID_reduction_nor, lu("0000")) == "1");
    REQUIRE(red(ID_reduction_nor, lu("01x0")) == "0");
    REQUIRE(red(ID_reduction_nor, lu("00z0")) == "x");
  }

  GIVEN("^ of four-valued operands is not folded")
  {
    // The verilog_simplifier lowers reduction_xor/xnor to $countones,
    // which is not folded for four-valued operands.
    REQUIRE(!verilog_constant_fold(unary_exprt{ID_reduction_xor, lu("0000"),
                                               one_bit})
               .is_constant());
    REQUIRE(!verilog_constant_fold(unary_exprt{ID_reduction_xnor, lu("0111"),
                                               one_bit})
               .is_constant());
  }

  GIVEN("two-valued operands yield Booleans")
  {
    auto folded = verilog_constant_fold(
      unary_exprt{ID_reduction_and, u(4, 15), bool_typet{}});
    REQUIRE(folded == true_exprt{});
    auto folded2 = verilog_constant_fold(
      unary_exprt{ID_reduction_xor, u(4, 7), bool_typet{}});
    REQUIRE(folded2 == true_exprt{});
    auto folded3 = verilog_constant_fold(
      unary_exprt{ID_reduction_or, u(4, 0), bool_typet{}});
    REQUIRE(folded3 == false_exprt{});
  }
}

SCENARIO("logical operators, 1800-2017 11.4.7")
{
  // The truth value of an operand: 1 if it has a known 1 digit, 0 if it has
  // no 1 and no x/z digit, and x otherwise.
  const auto T = lu("0100");
  const auto F = lu("0000");
  const auto X = lu("00x0");
  const auto T_with_x = lu("1x00"); // known nonzero, hence true

  GIVEN("!")
  {
    // The aval/bval encoding of ! yields x when the operand has an x/z
    // digit, and otherwise negates the least-significant digit only.
    // This differs from 11.4.7, under which ! of a vector with a known 1
    // digit is 0.
    REQUIRE(digits(verilog_constant_fold(lnot(T, one_bit))) == "1"); // !0100
    REQUIRE(digits(verilog_constant_fold(lnot(F, one_bit))) == "1"); // !0000
    REQUIRE(digits(verilog_constant_fold(lnot(X, one_bit))) == "x");
    REQUIRE(digits(verilog_constant_fold(lnot(T_with_x, one_bit))) == "x");
    // two-valued
    REQUIRE(verilog_constant_fold(not_exprt{true_exprt{}}) == false_exprt{});
    REQUIRE(verilog_constant_fold(not_exprt{false_exprt{}}) == true_exprt{});
  }

  GIVEN("&&, Table 11-18")
  {
    auto land = [&](const constant_exprt &a, const constant_exprt &b)
    { return digits(verilog_constant_fold(::land(a, b, one_bit))); };
    REQUIRE(land(T, T) == "1");
    REQUIRE(land(T, F) == "0");
    REQUIRE(land(F, T) == "0");
    REQUIRE(land(F, F) == "0");
    REQUIRE(land(X, F) == "0"); // 0 is controlling
    REQUIRE(land(F, X) == "0");
    REQUIRE(land(X, T) == "x");
    REQUIRE(land(T, X) == "x");
    REQUIRE(land(X, X) == "x");
    REQUIRE(land(T_with_x, T) == "1");
  }

  GIVEN("||, Table 11-19")
  {
    auto lor = [&](const constant_exprt &a, const constant_exprt &b)
    { return digits(verilog_constant_fold(::lor(a, b, one_bit))); };
    REQUIRE(lor(T, T) == "1");
    REQUIRE(lor(T, F) == "1");
    REQUIRE(lor(F, F) == "0");
    REQUIRE(lor(X, T) == "1"); // 1 is controlling
    REQUIRE(lor(T, X) == "1");
    REQUIRE(lor(X, F) == "x");
    REQUIRE(lor(F, X) == "x");
    REQUIRE(lor(X, X) == "x");
  }

  GIVEN("two-valued && and ||")
  {
    REQUIRE(
      verilog_constant_fold(and_exprt{true_exprt{}, false_exprt{}}) ==
      false_exprt{});
    REQUIRE(
      verilog_constant_fold(and_exprt{true_exprt{}, true_exprt{}}) ==
      true_exprt{});
    REQUIRE(
      verilog_constant_fold(or_exprt{false_exprt{}, true_exprt{}}) ==
      true_exprt{});
    REQUIRE(
      verilog_constant_fold(or_exprt{false_exprt{}, false_exprt{}}) ==
      false_exprt{});
    // more than two operands
    REQUIRE(
      verilog_constant_fold(
        and_exprt{true_exprt{}, true_exprt{}, false_exprt{}}) == false_exprt{});
  }

  GIVEN("->")
  {
    auto imp = [&](const constant_exprt &a, const constant_exprt &b)
    {
      return digits(
        verilog_constant_fold(bin(a, ID_verilog_implies, b, one_bit)));
    };
    REQUIRE(imp(T, T) == "1");
    REQUIRE(imp(T, F) == "0");
    REQUIRE(imp(F, T) == "1");
    REQUIRE(imp(F, F) == "1");
    // The aval/bval encoding yields x whenever either operand has an x/z
    // digit, so a controlling false antecedent or true consequent does
    // not apply, unlike 11.4.7.
    REQUIRE(imp(F, X) == "x");
    REQUIRE(imp(X, T) == "x");
    REQUIRE(imp(X, F) == "x");
    REQUIRE(imp(T, X) == "x");
  }

  GIVEN("<->")
  {
    auto iff = [&](const constant_exprt &a, const constant_exprt &b) {
      return digits(verilog_constant_fold(bin(a, ID_verilog_iff, b, one_bit)));
    };
    REQUIRE(iff(T, T) == "1");
    REQUIRE(iff(T, F) == "0");
    REQUIRE(iff(F, F) == "1");
    REQUIRE(iff(X, T) == "x");
    REQUIRE(iff(F, X) == "x");
  }

  GIVEN("Boolean xor, xnor, nand, nor as produced by the type checker")
  {
    // The simplifier folds a Boolean xor (it is a disequality), but
    // leaves xnor, nand and nor as is.
    REQUIRE(
      verilog_constant_fold(xor_exprt{true_exprt{}, false_exprt{}}) ==
      true_exprt{});
    REQUIRE(
      verilog_constant_fold(xor_exprt{true_exprt{}, true_exprt{}}) ==
      false_exprt{});
    REQUIRE(!verilog_constant_fold(binary_exprt{
                                     true_exprt{}, ID_xnor, true_exprt{},
                                     bool_typet{}})
               .is_constant());
    REQUIRE(!verilog_constant_fold(nand_exprt{true_exprt{}, true_exprt{}})
               .is_constant());
    REQUIRE(!verilog_constant_fold(nor_exprt{false_exprt{}, false_exprt{}})
               .is_constant());
  }
}

SCENARIO("relational operators, 1800-2017 11.4.4")
{
  auto rel =
    [](const constant_exprt &a, const irep_idt &id, const constant_exprt &b)
  {
    auto type = (is_four_valued(a.type()) || is_four_valued(b.type()))
                  ? typet{one_bit}
                  : typet{bool_typet{}};
    return digits(verilog_constant_fold(bin(a, id, b, type)));
  };

  GIVEN("unsigned comparison")
  {
    REQUIRE(rel(u(4, 3), ID_lt, u(4, 5)) == "1");
    REQUIRE(rel(u(4, 5), ID_lt, u(4, 3)) == "0");
    REQUIRE(rel(u(4, 5), ID_le, u(4, 5)) == "1");
    REQUIRE(rel(u(4, 5), ID_gt, u(4, 5)) == "0");
    REQUIRE(rel(u(4, 5), ID_ge, u(4, 5)) == "1");
    // 15 > 0 as unsigned
    REQUIRE(rel(u(4, 15), ID_gt, u(4, 0)) == "1");
  }

  GIVEN("signed comparison")
  {
    // 4'sb1111 is -1
    REQUIRE(rel(s(4, -1), ID_lt, s(4, 0)) == "1");
    REQUIRE(rel(s(4, -8), ID_lt, s(4, 7)) == "1");
    REQUIRE(rel(s(4, 7), ID_ge, s(4, -8)) == "1");
  }

  GIVEN("x in an operand gives x")
  {
    REQUIRE(rel(lu("00x1"), ID_lt, lu("0100")) == "x");
    REQUIRE(rel(lu("0001"), ID_lt, lu("01z0")) == "x");
    REQUIRE(rel(lu("0001"), ID_lt, lu("0100")) == "1");
    REQUIRE(rel(ls("1111"), ID_lt, ls("0000")) == "1");
  }
}

SCENARIO("equality operators, 1800-2017 11.4.5 and 11.4.6")
{
  GIVEN("== and != on two-valued operands")
  {
    REQUIRE(
      verilog_constant_fold(equal_exprt{u(4, 3), u(4, 3)}) == true_exprt{});
    REQUIRE(
      verilog_constant_fold(equal_exprt{u(4, 3), u(4, 4)}) == false_exprt{});
    REQUIRE(
      verilog_constant_fold(notequal_exprt{u(4, 3), u(4, 4)}) == true_exprt{});
    REQUIRE(
      verilog_constant_fold(equal_exprt{true_exprt{}, true_exprt{}}) ==
      true_exprt{});
  }

  GIVEN("== and != on four-valued operands")
  {
    auto eq = [](const constant_exprt &a, const constant_exprt &b)
    {
      return digits(
        verilog_constant_fold(bin(a, ID_verilog_logical_equality, b, one_bit)));
    };
    auto ne = [](const constant_exprt &a, const constant_exprt &b)
    {
      return digits(verilog_constant_fold(
        bin(a, ID_verilog_logical_inequality, b, one_bit)));
    };
    REQUIRE(eq(lu("0101"), lu("0101")) == "1");
    REQUIRE(eq(lu("0101"), lu("0100")) == "0");
    REQUIRE(eq(lu("010x"), lu("0101")) == "x");
    REQUIRE(eq(lu("0101"), lu("z101")) == "x");
    REQUIRE(eq(lu("010x"), lu("010x")) == "x"); // even if the digits agree
    REQUIRE(ne(lu("0101"), lu("0100")) == "1");
    REQUIRE(ne(lu("0101"), lu("0101")) == "0");
    REQUIRE(ne(lu("010x"), lu("0101")) == "x");
  }

  GIVEN("=== and !== compare x and z exactly")
  {
    auto ceq = [](const constant_exprt &a, const constant_exprt &b) {
      return verilog_constant_fold(verilog_case_equality_exprt{a, b});
    };
    auto cne = [](const constant_exprt &a, const constant_exprt &b) {
      return verilog_constant_fold(verilog_case_inequality_exprt{a, b});
    };
    REQUIRE(ceq(lu("01xz"), lu("01xz")) == true_exprt{});
    REQUIRE(ceq(lu("01xz"), lu("01zx")) == false_exprt{});
    REQUIRE(ceq(lu("010x"), lu("0101")) == false_exprt{});
    REQUIRE(ceq(lu("0101"), lu("0101")) == true_exprt{});
    REQUIRE(cne(lu("01xz"), lu("01zx")) == true_exprt{});
    REQUIRE(cne(lu("01xz"), lu("01xz")) == false_exprt{});
    // two-valued operands
    REQUIRE(ceq(u(4, 5), u(4, 5)) == true_exprt{});
    REQUIRE(cne(u(4, 5), u(4, 6)) == true_exprt{});
  }

  GIVEN("==? and !=? treat x and z in the right operand as wildcards")
  {
    auto weq = [](const constant_exprt &a, const constant_exprt &b)
    {
      return digits(verilog_constant_fold(
        bin(a, ID_verilog_wildcard_equality, b, one_bit)));
    };
    auto wne = [](const constant_exprt &a, const constant_exprt &b)
    {
      return digits(verilog_constant_fold(
        bin(a, ID_verilog_wildcard_inequality, b, one_bit)));
    };
    REQUIRE(weq(lu("0101"), lu("01xz")) == "1");
    REQUIRE(weq(lu("0111"), lu("01xz")) == "1");
    REQUIRE(weq(lu("1101"), lu("01xz")) == "0");
    REQUIRE(weq(lu("0101"), lu("0101")) == "1");
    REQUIRE(weq(lu("0101"), lu("0100")) == "0");
    // x in the left operand at a wildcard position does not matter
    REQUIRE(weq(lu("01x1"), lu("01x1")) == "1");
    // The aval/bval encoding ignores x/z in the left operand, so an x
    // at a non-wildcard position matches rather than giving x.
    REQUIRE(weq(lu("x101"), lu("0101")) == "1");
    // but a mismatch elsewhere decides
    REQUIRE(weq(lu("x100"), lu("0101")) == "0");
    REQUIRE(wne(lu("1101"), lu("01xz")) == "1");
    REQUIRE(wne(lu("0101"), lu("01xz")) == "0");
    REQUIRE(wne(lu("x101"), lu("0101")) == "0");
    // two-valued operands
    REQUIRE(weq(u(4, 5), u(4, 5)) == "1");
  }
}

SCENARIO("shift operators, 1800-2017 11.4.10")
{
  GIVEN("<<")
  {
    REQUIRE(value_of(verilog_constant_fold(shl_exprt{u(8, 1), u(8, 3)})) == 8);
    REQUIRE(
      value_of(verilog_constant_fold(shl_exprt{u(8, 255), u(8, 4)})) == 240);
    REQUIRE(
      value_of(verilog_constant_fold(shl_exprt{u(8, 255), u(8, 8)})) == 0);
    REQUIRE(
      value_of(verilog_constant_fold(shl_exprt{u(8, 255), u(8, 200)})) == 0);
    REQUIRE(
      digits(verilog_constant_fold(shl_exprt{lu("1x0z"), lu("0001")})) ==
      "x0z0");
  }

  GIVEN(">> fills with zeros")
  {
    REQUIRE(
      value_of(verilog_constant_fold(lshr_exprt{u(8, 128), u(8, 7)})) == 1);
    REQUIRE(
      value_of(verilog_constant_fold(lshr_exprt{s(8, -128), u(8, 7)})) == 1);
    REQUIRE(
      digits(verilog_constant_fold(lshr_exprt{lu("1x0z"), lu("0010")})) ==
      "001x");
  }

  GIVEN(">>> fills with the sign bit for signed operands")
  {
    REQUIRE(
      value_of(verilog_constant_fold(ashr_exprt{s(8, -128), u(8, 7)})) == -1);
    REQUIRE(
      value_of(verilog_constant_fold(ashr_exprt{s(8, 64), u(8, 7)})) == 0);
    REQUIRE(
      value_of(verilog_constant_fold(ashr_exprt{s(8, -1), u(8, 100)})) == -1);
    // The sign digit of a four-valued signed operand is x; the aval/bval
    // arithmetic shift fills with its aval, which is 0.
    REQUIRE(
      digits(verilog_constant_fold(ashr_exprt{ls("x101"), lu("0010")})) ==
      "00x1");
    // for unsigned operands >>> is a logical shift
    REQUIRE(
      value_of(verilog_constant_fold(ashr_exprt{u(8, 128), u(8, 7)})) == 1);
  }

  GIVEN("x in the shift distance gives all x")
  {
    auto expr = shl_exprt{lu("0001"), lu("000x")};
    REQUIRE(digits(verilog_constant_fold(expr)) == "xxxx");
  }

  GIVEN("a signed shift distance is not folded")
  {
    // The shift lowering keeps a plain shift, which the simplifier does
    // not fold for a signed (here negative-looking) distance.
    REQUIRE(
      !verilog_constant_fold(shl_exprt{u(8, 1), s(8, -1)}).is_constant());
  }
}

SCENARIO("concatenation and replication, 1800-2017 11.4.12")
{
  GIVEN("concatenation of two-valued operands")
  {
    auto expr = concatenation_exprt{{u(4, 10), u(4, 5)}, unsignedbv_typet{8}};
    REQUIRE(value_of(verilog_constant_fold(expr)) == 165);
    auto expr2 = concatenation_exprt{
      {true_exprt{}, u(3, 0), false_exprt{}}, unsignedbv_typet{5}};
    REQUIRE(value_of(verilog_constant_fold(expr2)) == 16);
  }

  GIVEN("concatenation with four-valued operands keeps x/z")
  {
    auto expr = concatenation_exprt{
      {lu("1x"), u(2, 1), lu("z0")}, verilog_unsignedbv_typet{6}};
    REQUIRE(digits(verilog_constant_fold(expr)) == "1x01z0");
  }

  GIVEN("replication")
  {
    auto expr = replication_exprt{u(32, 3), u(2, 2), unsignedbv_typet{6}};
    REQUIRE(digits(verilog_constant_fold(expr)) == "101010");
    auto expr2 =
      replication_exprt{u(32, 2), lu("x1"), verilog_unsignedbv_typet{4}};
    REQUIRE(digits(verilog_constant_fold(expr2)) == "x1x1");
  }

  GIVEN("zero replication inside a concatenation is not folded")
  {
    // The simplifier does not fold a concatenation that contains a
    // zero-width (zero-times) replication.
    auto zero_rep = replication_exprt{u(32, 0), u(1, 1), unsignedbv_typet{0}};
    auto expr =
      concatenation_exprt{{u(2, 2), zero_rep, u(2, 1)}, unsignedbv_typet{4}};
    REQUIRE(!verilog_constant_fold(expr).is_constant());
  }
}

SCENARIO("bit-selects and part-selects, 1800-2017 11.5.1")
{
  GIVEN("a bit-select on a vector [3:0]")
  {
    auto src = lu("1x0z");
    REQUIRE(
      digits(verilog_constant_fold(bit_select(src, u(32, 0), bool_typet{}))) ==
      "0"); // z becomes 0 in bool
    REQUIRE(
      digits(verilog_constant_fold(bit_select(src, u(32, 0), one_bit))) == "z");
    REQUIRE(
      digits(verilog_constant_fold(bit_select(src, u(32, 1), one_bit))) == "0");
    REQUIRE(
      digits(verilog_constant_fold(bit_select(src, u(32, 2), one_bit))) == "x");
    REQUIRE(
      digits(verilog_constant_fold(bit_select(src, u(32, 3), one_bit))) == "1");
    // out of range is x
    REQUIRE(
      digits(verilog_constant_fold(bit_select(src, u(32, 4), one_bit))) == "x");
    REQUIRE(
      digits(verilog_constant_fold(bit_select(src, s(32, -1), one_bit))) ==
      "x");
    // x in the index is x
    REQUIRE(
      digits(verilog_constant_fold(bit_select(src, lu("0x"), one_bit))) == "x");
  }

  GIVEN("a bit-select on a two-valued vector [3:0]")
  {
    auto src = u(4, 10); // 1010
    REQUIRE(
      verilog_constant_fold(bit_select(src, u(32, 1), bool_typet{})) ==
      true_exprt{});
    REQUIRE(
      verilog_constant_fold(bit_select(src, u(32, 0), bool_typet{})) ==
      false_exprt{});
    // out of range is 0
    REQUIRE(
      verilog_constant_fold(bit_select(src, u(32, 7), bool_typet{})) ==
      false_exprt{});
  }

  GIVEN("a bit-select on a vector [7:4]")
  {
    verilog_unsignedbv_typet type{4};
    type.offset(4);
    auto src = constant_exprt{"1x0z", type};
    REQUIRE(
      digits(verilog_constant_fold(bit_select(src, u(32, 4), one_bit))) == "z");
    REQUIRE(
      digits(verilog_constant_fold(bit_select(src, u(32, 7), one_bit))) == "1");
    REQUIRE(
      digits(verilog_constant_fold(bit_select(src, u(32, 0), one_bit))) == "x");
  }

  GIVEN("a bit-select on an increasing vector [0:3]")
  {
    // the declared index 0 is the most significant digit
    verilog_unsignedbv_typet type{4};
    type.offset(0);
    type.increasing(true);
    auto src = constant_exprt{"1x0z", type};
    REQUIRE(
      digits(verilog_constant_fold(bit_select(src, u(32, 0), one_bit))) == "1");
    REQUIRE(
      digits(verilog_constant_fold(bit_select(src, u(32, 1), one_bit))) == "x");
    REQUIRE(
      digits(verilog_constant_fold(bit_select(src, u(32, 3), one_bit))) == "z");
  }

  GIVEN("a part-select [msb:lsb] on a vector [7:0]")
  {
    auto src = lu("1x0z0110");
    auto ps = [&](int msb, int lsb)
    {
      auto width = msb - lsb + 1;
      return digits(verilog_constant_fold(part_select(
        src,
        u(32, msb),
        u(32, lsb),
        verilog_unsignedbv_typet{std::size_t(width)})));
    };
    REQUIRE(ps(7, 0) == "1x0z0110");
    REQUIRE(ps(7, 4) == "1x0z");
    REQUIRE(ps(3, 0) == "0110");
    REQUIRE(ps(5, 2) == "0z01");
    REQUIRE(ps(2, 2) == "1");
    // partially out of range: the missing digits are x
    REQUIRE(ps(9, 6) == "xx1x");
  }

  GIVEN("a part-select on a two-valued vector")
  {
    auto src = u(8, 0xA5); // 10100101
    auto expr = part_select(src, u(32, 7), u(32, 4), u4);
    REQUIRE(value_of(verilog_constant_fold(expr)) == 10);
    // out of range digits are 0 for two-valued types
    auto expr2 = part_select(src, u(32, 9), u(32, 6), u4);
    REQUIRE(value_of(verilog_constant_fold(expr2)) == 2);
  }

  GIVEN("a part-select on an increasing vector [0:7]")
  {
    verilog_unsignedbv_typet type{8};
    type.offset(0);
    type.increasing(true);
    auto src = constant_exprt{"1x0z0110", type};
    // [0:3] are the most significant four digits
    auto expr = part_select(src, u(32, 0), u(32, 3), lu4);
    REQUIRE(digits(verilog_constant_fold(expr)) == "1x0z");
    auto expr2 = part_select(src, u(32, 4), u(32, 7), lu4);
    REQUIRE(digits(verilog_constant_fold(expr2)) == "0110");
  }

  GIVEN("indexed part-selects +: and -: on a vector [7:0]")
  {
    auto src = lu("1x0z0110");
    auto plus = indexed_part_select(
      ID_verilog_indexed_part_select_plus, src, u(32, 2), u(32, 4), lu4);
    REQUIRE(digits(verilog_constant_fold(plus)) == "0z01"); // bits 5..2
    auto minus = indexed_part_select(
      ID_verilog_indexed_part_select_minus, src, u(32, 5), u(32, 4), lu4);
    REQUIRE(digits(verilog_constant_fold(minus)) == "0z01"); // bits 5..2
    auto plus_oor = indexed_part_select(
      ID_verilog_indexed_part_select_plus, src, u(32, 6), u(32, 4), lu4);
    REQUIRE(digits(verilog_constant_fold(plus_oor)) == "xx1x"); // bits 9..6
    auto x_index = indexed_part_select(
      ID_verilog_indexed_part_select_plus, src, lu("x"), u(32, 4), lu4);
    REQUIRE(digits(verilog_constant_fold(x_index)) == "xxxx");
  }
}

SCENARIO("conditional operator, 1800-2017 11.4.11")
{
  GIVEN("a known condition")
  {
    REQUIRE(
      value_of(
        verilog_constant_fold(if_exprt{true_exprt{}, u(4, 1), u(4, 2)})) == 1);
    REQUIRE(
      value_of(
        verilog_constant_fold(if_exprt{false_exprt{}, u(4, 1), u(4, 2)})) == 2);
    // a vector condition with an x/z digit is ambiguous in the aval/bval
    // encoding (even with a known 1 digit), so the result is all x, i.e.
    // 0 for a two-valued type, unlike 11.4.11
    REQUIRE(
      value_of(verilog_constant_fold(if_exprt{lu("1x"), u(4, 1), u(4, 2)})) ==
      0);
    REQUIRE(
      value_of(verilog_constant_fold(if_exprt{lu("00"), u(4, 1), u(4, 2)})) ==
      2);
    REQUIRE(
      value_of(verilog_constant_fold(if_exprt{u(4, 7), u(4, 1), u(4, 2)})) ==
      1);
  }

  GIVEN("an ambiguous condition yields all x")
  {
    // The aval/bval encoding yields all x for an ambiguous condition,
    // rather than the digit-wise combination of 11.4.11.
    auto expr = if_exprt{lu("0x"), lu("1100"), lu("1010")};
    REQUIRE(digits(verilog_constant_fold(expr)) == "xxxx");
    auto expr2 = if_exprt{lu("z"), lu("1x0z"), lu("1x1z")};
    REQUIRE(digits(verilog_constant_fold(expr2)) == "xxxx");
    auto expr3 = if_exprt{lu("x"), u(4, 12), u(4, 10)};
    expr3.type() = lu4;
    REQUIRE(digits(verilog_constant_fold(expr3)) == "xxxx");
  }

  GIVEN("real operands")
  {
    REQUIRE(
      to_double(verilog_constant_fold(
        if_exprt{true_exprt{}, real(1.5), real(2.5)})) == 1.5);
    REQUIRE(
      to_double(verilog_constant_fold(
        if_exprt{false_exprt{}, real(1.5), real(2.5)})) == 2.5);
    // not folded for an ambiguous condition
    auto expr = if_exprt{lu("x"), real(1.5), real(2.5)};
    REQUIRE(!verilog_constant_fold(expr).is_constant());
  }
}

SCENARIO("type casts, 1800-2017 6.12.2 and 11.8.3")
{
  GIVEN("widening a signed operand sign-extends")
  {
    REQUIRE(
      value_of(verilog_constant_fold(
        typecast_exprt{s(4, -1), signedbv_typet{8}})) == -1);
    REQUIRE(
      value_of(verilog_constant_fold(
        typecast_exprt{s(4, -1), unsignedbv_typet{8}})) == 255);
    REQUIRE(
      value_of(verilog_constant_fold(
        typecast_exprt{s(4, 5), signedbv_typet{8}})) == 5);
    // x and z are extended as such
    REQUIRE(
      digits(verilog_constant_fold(
        typecast_exprt{ls("x101"), verilog_signedbv_typet{8}})) == "xxxxx101");
    REQUIRE(
      digits(verilog_constant_fold(
        typecast_exprt{ls("z101"), verilog_signedbv_typet{8}})) == "zzzzz101");
  }

  GIVEN("widening an unsigned operand zero-extends")
  {
    REQUIRE(
      value_of(verilog_constant_fold(
        typecast_exprt{u(4, 15), signedbv_typet{8}})) == 15);
    REQUIRE(
      value_of(verilog_constant_fold(
        typecast_exprt{u(4, 15), unsignedbv_typet{8}})) == 15);
    REQUIRE(
      digits(verilog_constant_fold(typecast_exprt{
        lu("x101"), verilog_unsignedbv_typet{8}})) == "0000x101");
  }

  GIVEN("zero_extend, as generated for a signed operand in an unsigned context")
  {
    REQUIRE(
      value_of(verilog_constant_fold(
        zero_extend_exprt{s(4, -1), unsignedbv_typet{8}})) == 15);
    REQUIRE(
      digits(verilog_constant_fold(zero_extend_exprt{
        ls("x101"), verilog_unsignedbv_typet{8}})) == "0000x101");
  }

  GIVEN("narrowing truncates")
  {
    REQUIRE(
      value_of(verilog_constant_fold(typecast_exprt{u(8, 0xAB), u4})) == 0xB);
    REQUIRE(
      value_of(verilog_constant_fold(typecast_exprt{s(8, -2), s4})) == -2);
    REQUIRE(
      value_of(verilog_constant_fold(typecast_exprt{s(8, 100), s4})) == 4);
    REQUIRE(
      digits(verilog_constant_fold(typecast_exprt{lu("1x0z0110"), lu4})) ==
      "0110");
  }

  GIVEN("converting to a two-valued type: x becomes 0 and z becomes 1")
  {
    // The aval/bval encoding turns z into 1 (not 0) when converting to a
    // two-valued type, unlike 6.3.1. So 1x0z becomes 1001.
    REQUIRE(
      value_of(verilog_constant_fold(typecast_exprt{lu("1x0z"), u4})) == 9);
    REQUIRE(
      value_of(verilog_constant_fold(
        typecast_exprt{lu("1x0z"), unsignedbv_typet{8}})) == 9);
    REQUIRE(
      value_of(verilog_constant_fold(
        typecast_exprt{ls("1x0z"), signedbv_typet{8}})) == -7);
  }

  GIVEN("converting to a four-valued type")
  {
    REQUIRE(
      digits(verilog_constant_fold(typecast_exprt{u(4, 5), lu4})) == "0101");
    REQUIRE(
      digits(verilog_constant_fold(
        typecast_exprt{s(4, -1), verilog_signedbv_typet{8}})) == "11111111");
    REQUIRE(
      digits(verilog_constant_fold(typecast_exprt{true_exprt{}, lu4})) ==
      "0001");
  }

  GIVEN("converting to Boolean: a nonzero known value is true")
  {
    REQUIRE(
      verilog_constant_fold(typecast_exprt{u(4, 2), bool_typet{}}) ==
      true_exprt{});
    REQUIRE(
      verilog_constant_fold(typecast_exprt{u(4, 0), bool_typet{}}) ==
      false_exprt{});
    REQUIRE(
      verilog_constant_fold(typecast_exprt{lu("0x"), bool_typet{}}) ==
      false_exprt{});
    // The aval/bval conversion to Boolean treats a vector with an x/z
    // digit as false, unlike 11.4.7 under which a known 1 digit is true.
    REQUIRE(
      verilog_constant_fold(typecast_exprt{lu("1x"), bool_typet{}}) ==
      false_exprt{});
    REQUIRE(
      verilog_constant_fold(typecast_exprt{real(0.5), bool_typet{}}) ==
      true_exprt{});
    REQUIRE(
      verilog_constant_fold(typecast_exprt{real(0.0), bool_typet{}}) ==
      false_exprt{});
  }

  GIVEN("Boolean to vector")
  {
    REQUIRE(
      value_of(verilog_constant_fold(typecast_exprt{true_exprt{}, u4})) == 1);
    REQUIRE(
      value_of(verilog_constant_fold(typecast_exprt{false_exprt{}, s4})) == 0);
  }

  GIVEN("integer to real")
  {
    REQUIRE(
      to_double(verilog_constant_fold(
        typecast_exprt{s(8, -3), verilog_real_typet{}})) == -3.0);
    REQUIRE(
      to_double(verilog_constant_fold(
        typecast_exprt{u(8, 200), verilog_real_typet{}})) == 200.0);
    // A four-valued operand with an x/z digit is not folded when
    // converted to a real.
    REQUIRE(!verilog_constant_fold(
                 typecast_exprt{lu("1x"), verilog_real_typet{}})
               .is_constant());
  }

  GIVEN("real to integer rounds to the nearest, away from zero on ties")
  {
    REQUIRE(
      value_of(verilog_constant_fold(
        typecast_exprt{real(2.5), signedbv_typet{8}})) == 3);
    REQUIRE(
      value_of(verilog_constant_fold(
        typecast_exprt{real(-2.5), signedbv_typet{8}})) == -3);
    REQUIRE(
      value_of(verilog_constant_fold(
        typecast_exprt{real(2.4), signedbv_typet{8}})) == 2);
    REQUIRE(
      value_of(verilog_constant_fold(
        typecast_exprt{real(-2.4), signedbv_typet{8}})) == -2);
    REQUIRE(
      value_of(verilog_constant_fold(
        typecast_exprt{real(3.5), unsignedbv_typet{8}})) == 4);
    REQUIRE(
      value_of(verilog_constant_fold(
        typecast_exprt{real(300.0), unsignedbv_typet{8}})) == 44);
  }

  GIVEN("real to shortreal and back")
  {
    auto to_short = verilog_constant_fold(
      typecast_exprt{real(1.5), verilog_shortreal_typet{}});
    REQUIRE(to_short.is_constant());
    REQUIRE(to_short.type() == verilog_shortreal_typet{});
    auto back =
      verilog_constant_fold(typecast_exprt{to_short, verilog_real_typet{}});
    REQUIRE(to_double(back) == 1.5);
  }

  GIVEN("signing casts keep the digits")
  {
    auto expr = verilog_explicit_signing_cast_exprt{u(4, 15), s4};
    REQUIRE(value_of(verilog_constant_fold(expr)) == -1);
    auto expr2 = verilog_explicit_signing_cast_exprt{ls("1x01"), lu4};
    REQUIRE(digits(verilog_constant_fold(expr2)) == "1x01");
  }

  GIVEN("explicit type and size casts have converted operands")
  {
    auto expr = verilog_explicit_type_cast_exprt{u(8, 5), unsignedbv_typet{8}};
    REQUIRE(value_of(verilog_constant_fold(expr)) == 5);
    auto size_cast =
      verilog_explicit_size_cast_exprt{u(32, 8), u(8, 5), unsignedbv_typet{8}};
    REQUIRE(value_of(verilog_constant_fold(size_cast)) == 5);
  }
}

SCENARIO("unsized literals")
{
  GIVEN("'0, '1, 'x, 'z with a context width")
  {
    auto zero = verilog_unbased_unsized_literal_exprt{ID_0, u4};
    REQUIRE(value_of(verilog_constant_fold(zero)) == 0);
    auto one = verilog_unbased_unsized_literal_exprt{ID_1, u4};
    REQUIRE(value_of(verilog_constant_fold(one)) == 15);
    auto x = verilog_unbased_unsized_literal_exprt{ID_x, lu4};
    REQUIRE(digits(verilog_constant_fold(x)) == "xxxx");
    auto z = verilog_unbased_unsized_literal_exprt{ID_z, lu4};
    REQUIRE(digits(verilog_constant_fold(z)) == "zzzz");
  }

  GIVEN("an unsized literal as an operand")
  {
    auto expr =
      bitor_exprt{verilog_unbased_unsized_literal_exprt{ID_1, u4}, u(4, 0)};
    REQUIRE(value_of(verilog_constant_fold(expr)) == 15);
  }
}

SCENARIO("nested expressions and non-constants")
{
  GIVEN("a nested expression is folded bottom-up")
  {
    // (3 + 4) * 2 - 1 == 13
    auto expr = minus_exprt{
      mult_exprt{plus_exprt{u(8, 3), u(8, 4), unsignedbv_typet{8}}, u(8, 2)},
      u(8, 1)};
    REQUIRE(value_of(verilog_constant_fold(expr)) == 13);
  }

  GIVEN(
    "x propagates through nested arithmetic but not through a controlling &&")
  {
    auto x_sum = plus_exprt{lu("000x"), lu("0001"), lu4};
    auto expr = land(lu("0000"), x_sum, one_bit);
    REQUIRE(digits(verilog_constant_fold(expr)) == "0");
  }

  GIVEN("a symbol is left alone, but constant operands around it are folded")
  {
    auto sym = symbol_exprt{"s", unsignedbv_typet{8}};
    auto expr = plus_exprt{
      sym,
      plus_exprt{u(8, 1), u(8, 2), unsignedbv_typet{8}},
      unsignedbv_typet{8}};
    auto folded = verilog_constant_fold(expr);
    REQUIRE(!folded.is_constant());
    REQUIRE(folded.id() == ID_plus);
    REQUIRE(to_plus_expr(folded).op0() == sym);
    REQUIRE(value_of(to_plus_expr(folded).op1()) == 3);
  }

  GIVEN("an operator that is not supported is left alone")
  {
    auto expr = unary_exprt{
      ID_verilog_streaming_concatenation_left_to_right, u(4, 1), u4};
    auto folded = verilog_constant_fold(expr);
    REQUIRE(folded == expr);
  }

  GIVEN("the source location is kept")
  {
    source_locationt location;
    location.set_line(42);
    auto expr = plus_exprt{u(8, 1), u(8, 2), unsignedbv_typet{8}};
    expr.add_source_location() = location;
    auto folded = verilog_constant_fold(expr);
    REQUIRE(folded.source_location().get_line() == "42");
  }

  GIVEN("a constant is returned as is")
  {
    REQUIRE(verilog_constant_fold(u(4, 5)) == u(4, 5));
    REQUIRE(verilog_constant_fold(lu("01xz")) == lu("01xz"));
    REQUIRE(verilog_constant_fold(real(1.5)) == real(1.5));
  }
}

// Cross-check against the lowering-based constant folding, i.e.
// verilog_simplifier(verilog_lowering(expr)), on all combinations of
// small operands. The two must agree whenever both yield a constant.
// The result of the folder is lowered for the comparison.

static symbol_tablet symbol_table;
static namespacet ns{symbol_table};

static void require_agreement(const exprt &expr)
{
  INFO("expression: " << expr.pretty());

  auto folded = verilog_constant_fold(expr);

  exprt lowered;
  try
  {
    lowered = verilog_simplifier(verilog_lowering(expr), ns);
  }
  catch(...)
  {
    FAIL("the lowering-based folding threw an exception");
  }

  if(!lowered.is_constant())
    return; // the lowering-based folding gives up

  REQUIRE(folded.is_constant());

  // compare the lowered representations
  auto folded_lowered = verilog_lowering(folded);
  REQUIRE(folded_lowered.is_constant());

  // Compare as integers; a Boolean is 0 or 1. The lowering may yield a
  // Boolean for a one-bit four-valued result, which then has no x/z.
  auto as_integer = [](const exprt &constant) -> mp_integer
  {
    if(constant.type().id() == ID_bool)
      return constant.is_true() ? 1 : 0;
    auto &bv_type = to_bitvector_type(constant.type());
    return bvrep2integer(
      to_constant_expr(constant).get_value(), bv_type.get_width(), false);
  };

  REQUIRE(as_integer(folded_lowered) == as_integer(lowered));
}

static std::vector<constant_exprt>
all_two_valued(std::size_t width, bool is_signed)
{
  std::vector<constant_exprt> result;
  for(mp_integer i = 0; i < power(2, width); ++i)
  {
    if(is_signed)
      result.push_back(
        s(width, i >= power(2, width - 1) ? i - power(2, width) : i));
    else
      result.push_back(u(width, i));
  }
  return result;
}

static std::vector<constant_exprt> all_four_valued(std::size_t width)
{
  std::vector<constant_exprt> result;
  std::string digits(width, '0');
  const char digit_values[] = {'0', '1', 'x', 'z'};
  std::size_t count = 1;
  for(std::size_t i = 0; i < width; i++)
    count *= 4;
  for(std::size_t n = 0; n < count; n++)
  {
    auto m = n;
    for(std::size_t i = 0; i < width; i++)
    {
      digits[i] = digit_values[m % 4];
      m /= 4;
    }
    result.push_back(lu(digits));
  }
  return result;
}

SCENARIO("cross-check with lowering: two-valued binary operators")
{
  for(bool is_signed : {false, true})
  {
    auto operands = all_two_valued(3, is_signed);
    typet type =
      is_signed ? typet{signedbv_typet{3}} : typet{unsignedbv_typet{3}};

    for(auto &a : operands)
      for(auto &b : operands)
      {
        require_agreement(plus_exprt{a, b, type});
        require_agreement(minus_exprt{a, b});
        require_agreement(mult_exprt{a, b});
        require_agreement(bitand_exprt{a, b});
        require_agreement(bitor_exprt{a, b});
        require_agreement(bitxor_exprt{a, b});
        require_agreement(binary_relation_exprt{a, ID_lt, b});
        require_agreement(binary_relation_exprt{a, ID_le, b});
        require_agreement(binary_relation_exprt{a, ID_gt, b});
        require_agreement(binary_relation_exprt{a, ID_ge, b});
        require_agreement(equal_exprt{a, b});
        require_agreement(notequal_exprt{a, b});
        require_agreement(shl_exprt{a, b});
        require_agreement(lshr_exprt{a, b});
        require_agreement(ashr_exprt{a, b});
        require_agreement(concatenation_exprt{{a, b}, unsignedbv_typet{6}});
        if(value_of(b) != 0)
        {
          require_agreement(div_exprt{a, b});
          require_agreement(mod_exprt{a, b});
        }
      }
  }
}

SCENARIO("cross-check with lowering: two-valued unary operators and casts")
{
  for(bool is_signed : {false, true})
  {
    for(auto &a : all_two_valued(4, is_signed))
    {
      require_agreement(unary_minus_exprt{a});
      require_agreement(bitnot_exprt{a});
      require_agreement(unary_exprt{ID_reduction_and, a, bool_typet{}});
      require_agreement(unary_exprt{ID_reduction_or, a, bool_typet{}});
      require_agreement(unary_exprt{ID_reduction_xor, a, bool_typet{}});
      require_agreement(unary_exprt{ID_reduction_nand, a, bool_typet{}});
      require_agreement(unary_exprt{ID_reduction_nor, a, bool_typet{}});
      require_agreement(unary_exprt{ID_reduction_xnor, a, bool_typet{}});
      require_agreement(typecast_exprt{a, unsignedbv_typet{8}});
      require_agreement(typecast_exprt{a, signedbv_typet{8}});
      require_agreement(typecast_exprt{a, unsignedbv_typet{2}});
      require_agreement(typecast_exprt{a, signedbv_typet{2}});
      require_agreement(typecast_exprt{a, bool_typet{}});
      require_agreement(zero_extend_exprt{a, unsignedbv_typet{8}});
      require_agreement(replication_exprt{u(32, 2), a, unsignedbv_typet{8}});
      for(auto &b : all_two_valued(2, false))
        require_agreement(
          if_exprt{notequal_exprt{b, u(2, 0)}, a, bitnot_exprt{a}});
    }
  }
}

static bool digits_have_xz(const exprt &constant)
{
  return id2string(to_constant_expr(constant).get_value())
           .find_first_of("xz") != std::string::npos;
}

SCENARIO("cross-check with lowering: four-valued operators")
{
  // The aval/bval encoding and the folder agree on all operators for
  // operands without x/z. With x/z, the encoding differs from the folder
  // (and from 1800-2017) in the following cases, which are hence only
  // cross-checked without x/z:
  // * the truth value of a vector operand of ->, <->, and of a
  //   conversion to Boolean: the encoding yields x (or false) whenever
  //   the operand has an x/z digit, whereas a vector with a 1 digit is
  //   true (11.4.7), as the encoding implements for && and ||;
  // * ! of a vector with more than one digit, where the encoding negates
  //   the least significant digit only; this is not cross-checked;
  // * the conditional operator with an ambiguous condition, where the
  //   encoding yields all x rather than the digit-wise combination of
  //   11.4.11;
  // * wildcard equality with x/z in the left operand, which the
  //   encoding ignores;
  // * the conversion of x/z to two-valued types, where the encoding
  //   turns z into 1 rather than 0.
  auto operands = all_four_valued(2);

  for(auto &a : operands)
  {
    require_agreement(bitnot_exprt{a});
    require_agreement(unary_minus_exprt{a});
    if(!digits_have_xz(a))
    {
      require_agreement(typecast_exprt{a, bool_typet{}});
      require_agreement(typecast_exprt{a, unsignedbv_typet{4}});
      require_agreement(typecast_exprt{a, signedbv_typet{1}});
    }
    require_agreement(unary_exprt{ID_reduction_and, a, one_bit});
    require_agreement(unary_exprt{ID_reduction_or, a, one_bit});
    // The xor reductions are not included: the lowering-based folding
    // fails on them with four-valued operands.
    require_agreement(unary_exprt{ID_reduction_nand, a, one_bit});
    require_agreement(unary_exprt{ID_reduction_nor, a, one_bit});
    require_agreement(typecast_exprt{a, verilog_unsignedbv_typet{4}});
    require_agreement(typecast_exprt{a, verilog_unsignedbv_typet{1}});
    require_agreement(
      replication_exprt{u(32, 2), a, verilog_unsignedbv_typet{4}});

    for(auto &b : operands)
    {
      require_agreement(plus_exprt{a, b, verilog_unsignedbv_typet{2}});
      require_agreement(minus_exprt{a, b});
      require_agreement(mult_exprt{a, b});
      require_agreement(div_exprt{a, b});
      require_agreement(mod_exprt{a, b});
      require_agreement(bitand_exprt{a, b});
      require_agreement(bitor_exprt{a, b});
      require_agreement(bitxor_exprt{a, b});
      require_agreement(bitxnor_exprt{a, b});
      require_agreement(land(a, b, one_bit));
      require_agreement(lor(a, b, one_bit));
      if(!digits_have_xz(a) && !digits_have_xz(b))
      {
        require_agreement(bin(a, ID_verilog_implies, b, one_bit));
        require_agreement(bin(a, ID_verilog_iff, b, one_bit));
        require_agreement(bin(a, ID_verilog_wildcard_equality, b, one_bit));
        require_agreement(if_exprt{b, a, bitnot_exprt{a}});
      }
      require_agreement(bin(a, ID_verilog_logical_equality, b, one_bit));
      require_agreement(bin(a, ID_verilog_logical_inequality, b, one_bit));
      require_agreement(verilog_case_equality_exprt{a, b});
      require_agreement(verilog_case_inequality_exprt{a, b});
      require_agreement(bin(a, ID_lt, b, one_bit));
      require_agreement(bin(a, ID_ge, b, one_bit));
      require_agreement(shl_exprt{a, b});
      require_agreement(lshr_exprt{a, b});
      require_agreement(
        concatenation_exprt{{a, b}, verilog_unsignedbv_typet{4}});
      // a known condition, with x/z in the operands
      if(!digits_have_xz(b))
        require_agreement(if_exprt{b, a, bitnot_exprt{a}});
      // x/z only in the left operand of a wildcard equality is fine
      if(!digits_have_xz(a))
        require_agreement(bin(a, ID_verilog_wildcard_equality, b, one_bit));
    }
  }
}
