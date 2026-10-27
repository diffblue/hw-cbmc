/*******************************************************************\

Module: aval/bval Encoding Unit Tests

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/std_expr.h>

#include <testing-utils/use_catch.h>
#include <verilog/aval_bval_encoding.h>
#include <verilog/verilog_types.h>

/// helper: build an aval/bval constant for the given four-valued type
/// from separate aval and bval vectors
static constant_exprt aval_bval_constant(
  const typet &four_valued_type,
  const mp_integer &aval,
  const mp_integer &bval)
{
  auto type = lower_to_aval_bval(four_valued_type);
  auto width = aval_bval_width(type);
  auto value = aval + bval * power(2, width);
  return constant_exprt{integer2bvrep(value, width * 2), type};
}

SCENARIO("raise_from_aval_bval decodes the aval/bval bit pairs")
{
  GIVEN("a 1-bit four-valued type")
  {
    auto type = verilog_unsignedbv_typet{1};

    THEN("each of the four bit pairs yields the right digit")
    {
      // bval aval | 4-state Verilog value
      REQUIRE(
        raise_from_aval_bval(aval_bval_constant(type, 0, 0), type) ==
        constant_exprt{"0", type});
      REQUIRE(
        raise_from_aval_bval(aval_bval_constant(type, 1, 0), type) ==
        constant_exprt{"1", type});
      REQUIRE(
        raise_from_aval_bval(aval_bval_constant(type, 0, 1), type) ==
        constant_exprt{"x", type});
      REQUIRE(
        raise_from_aval_bval(aval_bval_constant(type, 1, 1), type) ==
        constant_exprt{"z", type});
    }
  }

  GIVEN("a 4-bit constant with all four digits")
  {
    auto type = verilog_unsignedbv_typet{4};
    // MSB first: 0 (a0 b0), 1 (a1 b0), x (a0 b1), z (a1 b1)
    auto src = aval_bval_constant(type, 0b0101, 0b0011);

    THEN("the digits are most-significant bit first")
    {
      auto raised = raise_from_aval_bval(src, type);
      REQUIRE(raised.get_value() == "01xz");
      REQUIRE(raised.type() == type);
    }
  }

  GIVEN("a signed four-valued type")
  {
    auto type = verilog_signedbv_typet{4};
    auto src = aval_bval_constant(type, 0b1001, 0b0100);

    THEN("the result has the signed four-valued type")
    {
      auto raised = raise_from_aval_bval(src, type);
      REQUIRE(raised.get_value() == "1x01");
      REQUIRE(raised.type() == verilog_signedbv_typet{4});
    }
  }

  GIVEN("a constant wider than 64 bits")
  {
    auto type = verilog_unsignedbv_typet{70};
    // bit 69 is z, bit 65 is 1, bit 0 is x, all others are 0
    auto aval = power(2, 69) + power(2, 65);
    auto bval = power(2, 69) + 1;
    auto src = aval_bval_constant(type, aval, bval);

    THEN("all digits are decoded")
    {
      auto expected = std::string(70, '0');
      expected[0] = 'z';
      expected[69 - 65] = '1';
      expected[69] = 'x';
      REQUIRE(raise_from_aval_bval(src, type).get_value() == expected);
    }
  }
}

SCENARIO("raise_from_aval_bval inverts lower_to_aval_bval")
{
  GIVEN("four-valued constants")
  {
    for(const auto &bits : {"0000", "1111", "0101", "x0z1", "xxxx", "zzzz"})
    {
      auto constant = constant_exprt{bits, verilog_unsignedbv_typet{4}};
      auto lowered = lower_to_aval_bval(constant);
      auto raised = raise_from_aval_bval(lowered, constant.type());
      REQUIRE(raised == constant);
      REQUIRE(raised.type() == verilog_unsignedbv_typet{4});
    }
  }

  GIVEN("a signed four-valued constant")
  {
    auto constant = constant_exprt{"1x01", verilog_signedbv_typet{4}};
    auto lowered = lower_to_aval_bval(constant);
    REQUIRE(raise_from_aval_bval(lowered, constant.type()) == constant);
  }

  GIVEN("a constant with ?")
  {
    // ? is a z (1800-2017 5.7.1)
    auto type = verilog_unsignedbv_typet{4};
    auto lowered = lower_to_aval_bval(constant_exprt{"1??0", type});
    REQUIRE(
      raise_from_aval_bval(lowered, type) == constant_exprt{"1zz0", type});
  }
}

SCENARIO("lower_to_aval_bval inverts raise_from_aval_bval")
{
  GIVEN("every aval/bval constant of width 3")
  {
    auto type = verilog_unsignedbv_typet{3};

    THEN("lowering the raised constant yields the original")
    {
      for(unsigned aval = 0; aval < 8; aval++)
        for(unsigned bval = 0; bval < 8; bval++)
        {
          auto src = aval_bval_constant(type, aval, bval);
          auto raised = raise_from_aval_bval(src, type);
          REQUIRE(lower_to_aval_bval(raised) == src);
          REQUIRE(aval_bval_has_xz(src) == (bval != 0));
        }
    }
  }
}
