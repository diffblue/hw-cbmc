/*******************************************************************\

Module: aval/bval encoding

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "aval_bval_encoding.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>
#include <util/std_expr.h>

bv_typet aval_bval_type(std::size_t width, irep_idt source_type)
{
  PRECONDITION(!source_type.empty());
  auto result = bv_typet{width * 2};
  result.set(ID_C_verilog_aval_bval, source_type);
  return result;
}

bv_typet lower_to_aval_bval(const typet &src)
{
  PRECONDITION(
    src.id() == ID_verilog_unsignedbv || src.id() == ID_verilog_signedbv);
  return aval_bval_type(to_bitvector_type(src).get_width(), src.id());
}

bool is_aval_bval(const typet &type)
{
  return type.id() == ID_bv && !type.get(ID_C_verilog_aval_bval).empty();
}

std::size_t aval_bval_width(const typet &type)
{
  PRECONDITION(is_aval_bval(type));
  return to_bv_type(type).get_width() / 2;
}

typet aval_bval_underlying(const typet &src)
{
  auto id = src.get(ID_C_verilog_aval_bval);
  if(id == ID_verilog_unsignedbv)
    return unsignedbv_typet{aval_bval_width(src)};
  else if(id == ID_verilog_signedbv)
    return signedbv_typet{aval_bval_width(src)};
  else
    PRECONDITION(false);
}

constant_exprt lower_to_aval_bval(const constant_exprt &src)
{
  PRECONDITION(
    src.type().id() == ID_verilog_signedbv ||
    src.type().id() == ID_verilog_unsignedbv);

  auto new_type = lower_to_aval_bval(src.type());
  auto width = aval_bval_width(new_type);
  auto &value = id2string(src.get_value());

  auto bv_f = [width, value](const std::size_t dest_index) {
    bool bval = dest_index >= width;
    std::size_t src_bit_nr = bval ? dest_index - width : dest_index;

    // bval aval | 4-state Verilog value
    // ----------|----------------------
    //   0    0  |   0
    //   0    1  |   1
    //   1    0  |   X
    //   1    1  |   Z

    switch(value[value.size() - 1 - src_bit_nr])
    {
    case '0':
      return bval ? 0 : 0;
    case '1':
      return bval ? 0 : 1;
    case 'x':
      return bval ? 1 : 0;
    case '?':
    case 'z':
      return bval ? 1 : 1;
    default:
      INVARIANT(false, "unexpected Verilog vector bit");
    }
  };

  return constant_exprt{make_bvrep(width * 2, bv_f), new_type};
}

exprt aval(const exprt &src)
{
  PRECONDITION(is_aval_bval(src.type()));
  auto width = aval_bval_width(src.type());
  return extractbits_exprt{
    src, from_integer(0, integer_typet()), bv_typet{width}};
}

exprt bval(const exprt &src)
{
  PRECONDITION(is_aval_bval(src.type()));
  auto width = aval_bval_width(src.type());
  return extractbits_exprt{
    src, from_integer(width, integer_typet()), bv_typet{width}};
}

static exprt adjust_size(const exprt &src, std::size_t dest_width)
{
  auto src_width = to_bv_type(src.type()).get_width();
  if(dest_width > src_width)
  {
    auto zeros = from_integer(0, bv_typet{dest_width - src_width});
    return concatenation_exprt{{zeros, src}, bv_typet{dest_width}};
  }
  else if(dest_width < src_width)
  {
    return extractbits_exprt{
      src, from_integer(0, integer_typet{}), bv_typet{dest_width}};
  }
  else
    return src;
}

static exprt
combine_aval_bval(const exprt &aval, const exprt &bval, const typet &dest)
{
  PRECONDITION(aval.type().id() == ID_bv);
  PRECONDITION(bval.type().id() == ID_bv);
  return concatenation_exprt{{bval, aval}, dest};
}

exprt aval_bval_conversion(const exprt &src, const typet &dest)
{
  PRECONDITION(is_aval_bval(src.type()));
  PRECONDITION(is_aval_bval(dest));

  auto src_width = aval_bval_width(src.type());
  auto dest_width = aval_bval_width(dest);

  if(src_width == dest_width)
  {
    // same size
    return typecast_exprt{src, dest};
  }
  else
  {
    auto new_aval = adjust_size(aval(src), dest_width);
    auto new_bval = adjust_size(bval(src), dest_width);
    return combine_aval_bval(new_aval, new_bval, dest);
  }
}

std::string decode_aval_bval(const constant_exprt &expr)
{
  PRECONDITION(is_aval_bval(expr.type()));
  auto width = aval_bval_width(expr.type());
  auto &src_value = expr.get_value();
  std::string result;
  result.reserve(width);

  for(std::size_t i = 0; i < width; i++)
  {
    auto bit_index = width - 1 - i;
    auto aval = get_bvrep_bit(src_value, width * 2, bit_index);
    auto bval = get_bvrep_bit(src_value, width * 2, bit_index + width);
    if(bval)
      result += aval ? 'x' : 'z';
    else
      result += aval ? '1' : '0';
  }

  return result;
}
