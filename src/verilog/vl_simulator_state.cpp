/*******************************************************************\

Module: Verilog Simulator State

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "vl_simulator_state.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/mp_arith.h>
#include <util/std_expr.h>

#include "verilog_expr.h"

static std::size_t type_width(const typet &type)
{
  if(type.id() == ID_bool)
    return 1;
  if(can_cast_type<bitvector_typet>(type))
    return to_bitvector_type(type).get_width();
  return 64;
}

mp_integer vl_simulator_statet::eval_expr(const exprt &expr)
{
  const irep_idt &id = expr.id();

  if(id == ID_constant)
  {
    const auto &c = to_constant_expr(expr);
    if(c.type().id() == ID_string)
      return 0;
    if(c.type().id() == ID_bool)
    {
      if(c.get_value() == ID_true)
        return 1;
      return 0;
    }
    if(
      c.type().id() == ID_verilog_unsignedbv ||
      c.type().id() == ID_verilog_signedbv)
    {
      const auto &bits = id2string(c.get_value());
      mp_integer result = 0;
      for(char b : bits)
      {
        result *= 2;
        if(b == '1')
          result += 1;
      }
      return result;
    }
    mp_integer val;
    if(!to_integer(c, val))
      return val;
    const auto &value_str = id2string(c.get_value());
    if(!value_str.empty())
    {
      bool all_digits = true;
      for(char ch : value_str)
        if(ch < '0' || ch > '9')
        {
          all_digits = false;
          break;
        }
      if(all_digits)
        return string2integer(value_str);
    }
    return 0;
  }
  else if(id == ID_symbol)
  {
    auto it = state.find(to_symbol_expr(expr).identifier());
    if(it != state.end())
      return it->second;
    return 0;
  }
  else if(id == ID_verilog_identifier)
  {
    const auto &vid = to_verilog_identifier_expr(expr);
    if(!vid.scope().empty())
    {
      auto full_id = irep_idt{"Verilog::$root." + id2string(vid.scope())};
      auto it = state.find(full_id);
      if(it != state.end())
        return it->second;
      it = state.find(vid.scope());
      if(it != state.end())
        return it->second;
    }
    auto it = state.find(vid.base_name());
    if(it != state.end())
      return it->second;
    return 0;
  }
  else if(id == ID_plus)
  {
    mp_integer result = 0;
    for(const auto &op : expr.operands())
      result += eval_expr(op);
    return result;
  }
  else if(id == ID_minus)
  {
    if(expr.operands().size() == 1)
      return -eval_expr(expr.operands()[0]);
    return eval_expr(expr.operands()[0]) - eval_expr(expr.operands()[1]);
  }
  else if(id == ID_mult)
  {
    mp_integer result = 1;
    for(const auto &op : expr.operands())
      result *= eval_expr(op);
    return result;
  }
  else if(id == ID_div)
  {
    mp_integer lhs = eval_expr(expr.operands()[0]);
    mp_integer rhs = eval_expr(expr.operands()[1]);
    if(rhs == 0)
      return 0;
    return lhs / rhs;
  }
  else if(id == ID_mod)
  {
    mp_integer lhs = eval_expr(expr.operands()[0]);
    mp_integer rhs = eval_expr(expr.operands()[1]);
    if(rhs == 0)
      return 0;
    return lhs % rhs;
  }
  else if(id == ID_equal)
    return mp_integer{
      eval_expr(expr.operands()[0]) == eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_notequal)
    return mp_integer{
      eval_expr(expr.operands()[0]) != eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_le)
    return mp_integer{
      eval_expr(expr.operands()[0]) <= eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_lt)
    return mp_integer{
      eval_expr(expr.operands()[0]) < eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_ge)
    return mp_integer{
      eval_expr(expr.operands()[0]) >= eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_gt)
    return mp_integer{
      eval_expr(expr.operands()[0]) > eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_not)
    return mp_integer{eval_expr(expr.operands()[0]) == 0 ? 1 : 0};
  else if(id == ID_and)
  {
    for(const auto &op : expr.operands())
      if(eval_expr(op) == 0)
        return 0;
    return 1;
  }
  else if(id == ID_or)
  {
    for(const auto &op : expr.operands())
      if(eval_expr(op) != 0)
        return 1;
    return 0;
  }
  else if(id == ID_bitand)
  {
    mp_integer result = eval_expr(expr.operands()[0]);
    for(std::size_t i = 1; i < expr.operands().size(); ++i)
      result = bitwise_and(result, eval_expr(expr.operands()[i]));
    return result;
  }
  else if(id == ID_bitor)
  {
    mp_integer result = eval_expr(expr.operands()[0]);
    for(std::size_t i = 1; i < expr.operands().size(); ++i)
      result = bitwise_or(result, eval_expr(expr.operands()[i]));
    return result;
  }
  else if(id == ID_bitxor)
  {
    mp_integer result = eval_expr(expr.operands()[0]);
    for(std::size_t i = 1; i < expr.operands().size(); ++i)
      result = bitwise_xor(result, eval_expr(expr.operands()[i]));
    return result;
  }
  else if(id == ID_bitnot)
  {
    mp_integer v = eval_expr(expr.operands()[0]);
    std::size_t width = type_width(expr.type());
    mp_integer mask = power(2, mp_integer{width}) - 1;
    return bitwise_xor(v, mask);
  }
  else if(id == ID_lshr)
  {
    std::size_t width = type_width(expr.type());
    return logic_right_shift(
      eval_expr(expr.operands()[0]), eval_expr(expr.operands()[1]), width);
  }
  else if(id == ID_shr)
  {
    std::size_t width = type_width(expr.type());
    return logic_right_shift(
      eval_expr(expr.operands()[0]), eval_expr(expr.operands()[1]), width);
  }
  else if(id == ID_shl)
  {
    std::size_t width = type_width(expr.type());
    return logic_left_shift(
      eval_expr(expr.operands()[0]), eval_expr(expr.operands()[1]), width);
  }
  else if(id == ID_ashr)
  {
    std::size_t width = type_width(expr.type());
    return arith_right_shift(
      eval_expr(expr.operands()[0]), eval_expr(expr.operands()[1]), width);
  }
  else if(id == ID_typecast)
    return eval_expr(expr.operands()[0]);
  else if(id == ID_extractbits)
  {
    mp_integer val = eval_expr(expr.operands()[0]);
    mp_integer upper = eval_expr(expr.operands()[1]);
    mp_integer lower = eval_expr(expr.operands()[2]);
    mp_integer slice_width = upper - lower + 1;
    std::size_t sw = numeric_cast_v<std::size_t>(slice_width);
    mp_integer mask = power(2, mp_integer{sw}) - 1;
    mp_integer shifted =
      logic_right_shift(val, lower, type_width(expr.operands()[0].type()));
    return bitwise_and(shifted, mask);
  }
  else if(id == ID_index)
  {
    mp_integer val = eval_expr(expr.operands()[0]);
    mp_integer idx = eval_expr(expr.operands()[1]);
    mp_integer shifted =
      logic_right_shift(val, idx, type_width(expr.operands()[0].type()));
    return bitwise_and(shifted, mp_integer{1});
  }
  else if(id == ID_concatenation)
  {
    mp_integer result = 0;
    for(const auto &op : expr.operands())
    {
      std::size_t width = type_width(op.type());
      result = logic_left_shift(result, mp_integer{width}, 128);
      result = bitwise_or(result, eval_expr(op));
    }
    return result;
  }
  else if(id == ID_verilog_logical_equality)
    return mp_integer{
      eval_expr(expr.operands()[0]) == eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_verilog_logical_inequality)
    return mp_integer{
      eval_expr(expr.operands()[0]) != eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_verilog_case_equality)
    return mp_integer{
      eval_expr(expr.operands()[0]) == eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_verilog_case_inequality)
    return mp_integer{
      eval_expr(expr.operands()[0]) != eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_if)
  {
    mp_integer cond = eval_expr(expr.operands()[0]);
    return cond != 0 ? eval_expr(expr.operands()[1])
                     : eval_expr(expr.operands()[2]);
  }

  return 0;
}
