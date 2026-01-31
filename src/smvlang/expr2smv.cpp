/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "expr2smv.h"
#include "expr2smv_class.h"

#include <util/mathematical_types.h>

#include <temporal-logic/ltl.h>

#include "smv_expr.h"
#include "smv_types.h"

/*******************************************************************\

Function: expr2smvt::convert_smv_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_smv_set(const smv_set_exprt &src)
{
  std::string dest = "{ ";

  bool first=true;

  forall_operands(it, src)
  {
    if(first)
      first=false;
    else
      dest+=", ";

    dest += convert_rec(*it).s;
  }

  dest+=" }";
  return {precedencet::MAX, std::move(dest)};
}

/*******************************************************************\

Function: expr2smvt::convert_cond

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_cond(const exprt &src)
{
  std::string dest = "case ";

  bool condition=true;

  forall_operands(it, src)
  {
    dest += convert_rec(*it).s;

    if(condition)
      dest+=": ";
    else
      dest+="; ";
    
    condition=!condition;
  }

  dest+="esac";
  return {precedencet::MAX, std::move(dest)};
}

/*******************************************************************\

Function: expr2smvt::convert_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_binary(
  const binary_exprt &src,
  const std::string &symbol,
  precedencet precedence)
{
  std::string dest;

  {
    // lhs
    auto lhs_rec = convert_rec(src.lhs());

    if(precedence >= lhs_rec.p)
      dest += '(';

    dest += lhs_rec.s;

    if(precedence >= lhs_rec.p)
      dest += ')';
  }

  dest += ' ';
  dest += symbol;
  dest += ' ';

  {
    // rhs
    auto rhs_rec = convert_rec(src.rhs());

    if(precedence >= rhs_rec.p)
      dest += '(';

    dest += rhs_rec.s;

    if(precedence >= rhs_rec.p)
      dest += ')';
  }

  return {precedence, std::move(dest)};
}

/*******************************************************************\

Function: expr2smvt::convert_binary_ctl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_binary_ctl(
  const binary_exprt &src,
  const std::string &symbol)
{
  PRECONDITION(symbol.size() == 2);
  PRECONDITION(symbol[0] == 'A' || symbol[0] == 'E');
  /* R is not part of the NuSMV grammar */
  PRECONDITION(symbol[1] == 'U' || symbol[1] == 'R');

  auto dest =
    symbol.substr(0, 1) + " [" +
    convert_binary(src, symbol.substr(1, 1), precedencet::TEMPORAL).s + ']';

  return {precedencet::TEMPORAL, std::move(dest)};
}

/*******************************************************************\

Function: expr2smvt::convert_binary_associative

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_binary_associative(
  const exprt &src,
  const std::string &symbol,
  precedencet precedence)
{
  if(src.operands().size()<2)
    return convert_norep(src);

  bool first=true;

  std::string dest;

  forall_operands(it, src)
  {
    if(first)
      first=false;
    else
    {
      dest+=' ';
      dest+=symbol;
      dest+=' ';
    }

    auto op_rec = convert_rec(*it);

    // clang-format off
    bool use_parentheses =
        src.id() == it->id() ? false
      : precedence >= op_rec.p;
    // clang-format on

    if(use_parentheses)
      dest += '(';

    dest += op_rec.s;

    if(use_parentheses)
      dest += ')';
  }

  return {precedence, std::move(dest)};
}

/*******************************************************************\

Function: expr2smvt::convert_function_application

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_function_application(
  const std::string &symbol,
  const exprt &src)
{
  bool first = true;

  std::string dest = symbol + '(';

  for(auto &op : src.operands())
  {
    if(first)
      first = false;
    else
    {
      dest += ',';
      dest += ' ';
    }

    auto op_rec = convert_rec(op);
    dest += op_rec.s;
  }

  return {precedencet::MAX, dest + ')'};
}

/*******************************************************************\

Function: expr2smvt::convert_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_typecast(const typecast_exprt &expr)
{
  // typecasts can repesent a variety of functions
  auto &src_type = expr.op().type();
  auto &dest_type = expr.type();

  if(src_type.id() == ID_unsignedbv && dest_type.id() == ID_signedbv)
  {
    // unsigned to signed
    auto src_width = to_unsignedbv_type(src_type).get_width();
    auto dest_width = to_signedbv_type(dest_type).get_width();

    if(src_width == dest_width)
    {
      // signedness change only
      return convert_rec(smv_signed_cast_exprt{expr.op(), dest_type});
    }
    else if(dest_width > src_width)
    {
      // Signedness _and_ width change. First go to signed, then extend.
      return convert_rec(smv_extend_exprt{
        smv_signed_cast_exprt{expr.op(), signedbv_typet{src_width}},
        dest_width - src_width,
        dest_type});
    }
    else
    {
      // First shrink, then go signed.
      return convert_rec(smv_signed_cast_exprt{
        smv_resize_exprt{expr.op(), dest_width, unsignedbv_typet{dest_width}},
        dest_type});
    }
  }
  else if(src_type.id() == ID_signedbv && dest_type.id() == ID_unsignedbv)
  {
    // signed to unsigned
    auto src_width = to_signedbv_type(src_type).get_width();
    auto dest_width = to_unsignedbv_type(dest_type).get_width();

    if(
      to_signedbv_type(src_type).get_width() ==
      to_unsignedbv_type(dest_type).get_width())
    {
      // signedness change only
      return convert_rec(smv_unsigned_cast_exprt{expr.op(), dest_type});
    }
    else if(dest_width > src_width)
    {
      // Signedness _and_ width change.
      // First enlarge, then go unsigned.
      return convert_rec(smv_unsigned_cast_exprt{
        smv_extend_exprt{
          expr.op(), dest_width - src_width, signedbv_typet{dest_width}},
        dest_type});
    }
    else
    {
      // First go unsigned, then shrink
      return convert_rec(smv_resize_exprt{
        smv_unsigned_cast_exprt{expr.op(), unsignedbv_typet{src_width}},
        dest_width,
        dest_type});
    }
  }
  else if(src_type.id() == ID_signedbv && dest_type.id() == ID_signedbv)
  {
    // signed to signed, width change.
    auto src_width = to_signedbv_type(src_type).get_width();
    auto dest_width = to_signedbv_type(dest_type).get_width();
    if(dest_width > src_width)
    {
      // enlarge using extend
      return convert_rec(
        smv_extend_exprt{expr.op(), dest_width - src_width, dest_type});
    }
    else
    {
      // Note that SMV's resize(...) preserves the sign bit, unlike our typecast.
      // We therefore first go unsigned, then resize, then go signed again.
      return convert_rec(smv_signed_cast_exprt{
        smv_resize_exprt{
          smv_unsigned_cast_exprt{expr.op(), unsignedbv_typet{src_width}},
          dest_width,
          unsignedbv_typet{dest_width}},
        dest_type});
    }
  }
  else if(src_type.id() == ID_unsignedbv && dest_type.id() == ID_unsignedbv)
  {
    // Unsigned to unsigned, width change. Use extend when enlarging.
    auto src_width = to_unsignedbv_type(src_type).get_width();
    auto dest_width = to_unsignedbv_type(dest_type).get_width();
    if(dest_width > src_width)
    {
      return convert_rec(
        smv_extend_exprt{expr.op(), dest_width - src_width, dest_type});
    }
    else
    {
      return convert_rec(smv_resize_exprt{expr.op(), dest_width, dest_type});
    }
  }
  else if(
    src_type.id() == ID_smv_enumeration && dest_type.id() == ID_smv_enumeration)
  {
    // added by SMV typechecker, implicit
    return convert_rec(expr.op());
  }
  else
    return convert_norep(expr);
}

/*******************************************************************\

Function: expr2smvt::convert_zero_extend

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_zero_extend(const zero_extend_exprt &expr)
{
  // Both "extend" and "resize" do sign extension.
  // Hence, use lowering.
  return convert_rec(expr.lower());
}

/*******************************************************************\

Function: expr2smvt::convert_rtctl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_rtctl(
  const ternary_exprt &src,
  const std::string &symbol,
  precedencet precedence)
{
  std::string op0 = convert_rec(src.op0()).s;
  std::string op1 = convert_rec(src.op1()).s;
  std::string op2 = convert_rec(src.op2()).s;
  return {precedence, symbol + ' ' + op0 + ".." + op1 + ' ' + op2};
}

/*******************************************************************\

Function: expr2smvt::convert_rtctl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_rtctl(
  const multi_ary_exprt &src,
  const std::string &symbol1,
  const std::string &symbol2,
  precedencet precedence)
{
  std::string op0 = convert_rec(src.op0()).s;
  std::string op1 = convert_rec(src.op1()).s;
  std::string op2 = convert_rec(src.op2()).s;
  std::string op3 = convert_rec(src.op3()).s;
  return {
    precedence,
    symbol1 + '[' + op0 + ' ' + symbol2 + ' ' + op1 + ".." + op2 + ' ' + op3 +
      ']'};
}

/*******************************************************************\

Function: expr2smvt::convert_unary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_unary(
  const unary_exprt &src,
  const std::string &symbol,
  precedencet precedence)
{
  auto &op = src.op();

  auto op_rec = convert_rec(op);

  // We special-case negation (!), since the precedence
  // of this operator changed between CMU SMV and NuSMV.

  // clang-format off
  bool parentheses =
      op.operands().size() == 1 ? false
    : src.id() == ID_not && !op.operands().empty() ? true
    : precedence >= op_rec.p;
  // clang-format on

  std::string dest = symbol;

  if(parentheses)
    dest += '(';

  dest += op_rec.s;

  if(parentheses)
    dest += ')';

  return {precedence, std::move(dest)};
}

/*******************************************************************\

Function: expr2smvt::convert_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt
expr2smvt::convert_index(const index_exprt &src, precedencet precedence)
{
  auto op0_rec = convert_rec(src.op0());

  std::string dest;

  if(precedence > op0_rec.p)
    dest += '(';
  dest += op0_rec.s;
  if(precedence > op0_rec.p)
    dest += ')';

  auto op1_rec = convert_rec(src.op1());

  dest+='[';
  dest += op1_rec.s;
  dest+=']';

  return {precedence, std::move(dest)};
}

/*******************************************************************\

Function: expr2smvt::convert_extractbits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_extractbits(const extractbits_exprt &expr)
{
  const precedencet precedence = precedencet::INDEX;
  auto op_rec = convert_rec(expr.src());

  std::string dest;

  if(precedence >= op_rec.p)
    dest += '(';
  dest += op_rec.s;
  if(precedence >= op_rec.p)
    dest += ')';

  dest += '[';

  // We can only do constant indices.
  if(expr.index().is_constant())
  {
    auto index_int = numeric_cast_v<mp_integer>(to_constant_expr(expr.index()));
    auto width = to_unsignedbv_type(expr.type()).get_width();
    dest += integer2string(index_int + width - 1);
    dest += ':';
    dest += integer2string(index_int);
  }
  else
  {
    dest += "?:?";
  }

  dest += ']';

  return {precedence, std::move(dest)};
}

/*******************************************************************\

Function: expr2smvt::convert_smv_bit_select

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt
expr2smvt::convert_smv_bit_selection(const ternary_exprt &expr)
{
  const precedencet precedence = precedencet::INDEX;
  auto op_rec = convert_rec(expr.op0());

  std::string dest;

  if(precedence >= op_rec.p)
    dest += '(';
  dest += op_rec.s;
  if(precedence >= op_rec.p)
    dest += ')';

  dest += '[';
  dest += convert_rec(expr.op1()).s;
  dest += ':';
  dest += convert_rec(expr.op2()).s;
  dest += ']';

  return {precedence, std::move(dest)};
}

/*******************************************************************\

Function: expr2smvt::convert_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt
expr2smvt::convert_if(const if_exprt &src, precedencet precedence)
{
  auto cond_rec = convert_rec(src.cond());

  std::string dest;

  if(precedence >= cond_rec.p)
    dest += '(';
  dest += cond_rec.s;
  if(precedence >= cond_rec.p)
    dest += ')';
  dest += '?';

  auto true_case_rec = convert_rec(src.true_case());

  dest += true_case_rec.s;
  dest += ':';

  auto false_case_rec = convert_rec(src.false_case());

  if(precedence > false_case_rec.p)
    dest += '(';
  dest += false_case_rec.s;
  if(precedence > false_case_rec.p)
    dest += ')';

  return {precedence, std::move(dest)};
}

/*******************************************************************\

Function: expr2smvt::convert_norep

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_norep(const exprt &src)
{
  return {precedencet::MAX, src.pretty()};
}

/*******************************************************************\

Function: expr2smvt::convert_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_symbol(const symbol_exprt &src)
{
  auto &symbol = ns.lookup(src);

  return {precedencet::MAX, id2string(symbol.display_name())};
}

/*******************************************************************\

Function: expr2smvt::convert_next_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_next_symbol(const exprt &src)
{
  auto tmp_rec =
    convert_symbol(symbol_exprt{src.get(ID_identifier), src.type()});

  return {precedencet::MAX, "next(" + tmp_rec.s + ")"};
}

/*******************************************************************\

Function: expr2smvt::convert_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_constant(const constant_exprt &src)
{
  const typet &type = src.type();

  std::string dest;

  if(type.id()==ID_bool)
  {
    if(src.is_true())
      dest+="TRUE";
    else
      dest+="FALSE";
  }
  else if(
    type.id() == ID_integer || type.id() == ID_natural ||
    type.id() == ID_range || type.id() == ID_smv_enumeration)
  {
    dest = id2string(src.get_value());
  }
  else if(type.id() == ID_signedbv || type.id() == ID_unsignedbv)
  {
    auto value_int = numeric_cast_v<mp_integer>(src);
    auto value_abs = value_int < 0 ? -value_int : value_int;
    auto minus = value_int < 0 ? "-" : "";
    auto sign_specifier = type.id() == ID_signedbv ? 's' : 'u';
    auto word_width = to_bitvector_type(type).width();
    dest = minus + std::string("0") + sign_specifier + 'd' +
           std::to_string(word_width) + '_' + integer2string(value_abs);
  }
  else if(type.id() == ID_bv)
  {
    auto &bv_type = to_bv_type(type);
    auto width = bv_type.width();
    auto &src_value = src.get_value();
    dest = std::string("0ub");
    dest += std::to_string(width);
    dest += '_';
    for(std::size_t i = 0; i < width; i++)
    {
      bool bit = get_bvrep_bit(src_value, width, width - i - 1);
      dest += bit ? '1' : '0';
    }
  }
  else
    return convert_norep(src);

  return {precedencet::MAX, std::move(dest)};
}

/*******************************************************************\

Function: expr2smvt::convert_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_rec(const exprt &src)
{
  if(src.id()==ID_plus)
    return convert_binary_associative(src, "+", precedencet::PLUS);

  else if(src.id()==ID_minus)
    return convert_binary_associative(src, "-", precedencet::PLUS);

  else if(src.id()==ID_unary_minus)
  {
    if(src.operands().size()!=1)
      return convert_norep(src);
    else
      return convert_unary(to_unary_minus_expr(src), "-", precedencet::UMINUS);
  }

  else if(src.id()==ID_index)
    return convert_index(to_index_expr(src), precedencet::INDEX);

  else if(src.id() == ID_mult)
    return convert_binary_associative(src, src.id_string(), precedencet::MULT);

  else if(src.id() == ID_div)
    return convert_binary(to_div_expr(src), src.id_string(), precedencet::MULT);

  else if(src.id() == ID_mod)
    return convert_binary(to_mod_expr(src), src.id_string(), precedencet::MULT);

  else if(src.id() == ID_smv_range)
    return convert_binary(to_smv_range_expr(src), "..", precedencet::UNION);
  // precedence is unknown

  else if(src.id() == ID_smv_set)
    return convert_smv_set(to_smv_set_expr(src));

  else if(src.id() == ID_smv_setin)
    return convert_binary(to_smv_setin_expr(src), "in", precedencet::IN);

  else if(src.id() == ID_smv_setnotin)
    return convert_binary(to_binary_expr(src), "notin", precedencet::IN);

  else if(src.id() == ID_smv_union)
    return convert_binary(to_smv_union_expr(src), "union", precedencet::UNION);

  else if(src.id()==ID_lt || src.id()==ID_gt ||
          src.id()==ID_le || src.id()==ID_ge)
    return convert_binary(
      to_binary_expr(src), src.id_string(), precedencet::REL);

  else if(src.id()==ID_equal)
  {
    auto &equal_expr = to_equal_expr(src);

    if(equal_expr.get_bool(ID_C_smv_iff))
      return convert_binary(equal_expr, "<->", precedencet::IFF);
    else
      return convert_binary(equal_expr, "=", precedencet::REL);
  }

  else if(src.id()==ID_notequal)
    return convert_binary(to_notequal_expr(src), "!=", precedencet::REL);

  else if(src.id() == ID_not || src.id() == ID_bitnot)
    return convert_unary(to_unary_expr(src), "!", precedencet::NOT);

  else if(src.id() == ID_and || src.id() == ID_bitand)
    return convert_binary_associative(src, "&", precedencet::AND);

  else if(src.id() == ID_or || src.id() == ID_bitor)
    return convert_binary_associative(src, "|", precedencet::OR);

  else if(src.id() == ID_implies || src.id() == ID_smv_bitimplies)
    return convert_binary(to_binary_expr(src), "->", precedencet::IMPLIES);

  else if(src.id() == ID_xor || src.id() == ID_bitxor)
    return convert_binary_associative(src, "xor", precedencet::OR);

  else if(src.id() == ID_xnor || src.id() == ID_bitxnor)
  {
    auto &binary_expr = to_binary_expr(src);

    if(src.get_bool(ID_C_smv_iff))
      return convert_binary(binary_expr, "<->", precedencet::IFF);
    else
      return convert_binary(binary_expr, "xnor", precedencet::OR);
  }

  else if(
    src.id() == ID_AG || src.id() == ID_EG || src.id() == ID_AF ||
    src.id() == ID_EF || src.id() == ID_AX || src.id() == ID_EX ||
    src.id() == ID_G || src.id() == ID_F || src.id() == ID_X)
  {
    return convert_unary(
      to_unary_expr(src), src.id_string() + " ", precedencet::TEMPORAL);
  }

  else if(
    src.id() == ID_smv_H || src.id() == ID_smv_O || src.id() == ID_smv_Y ||
    src.id() == ID_smv_Z)
  {
    return convert_unary(
      to_unary_expr(src),
      std::string(src.id_string(), 4, std::string::npos) + " ",
      precedencet::TEMPORAL);
  }

  else if(src.id() == ID_smv_bounded_H || src.id() == ID_smv_bounded_O)
  {
    return convert_unary(
      to_unary_expr(src),
      std::string(src.id_string(), 12, std::string::npos) + " ",
      precedencet::TEMPORAL);
  }

  else if(src.id() == ID_U)
  {
    return convert_binary(
      to_U_expr(src), src.id_string(), precedencet::TEMPORAL);
  }

  else if(
    src.id() == ID_AU || src.id() == ID_EU || src.id() == ID_AR ||
    src.id() == ID_ER)
  {
    return convert_binary_ctl(to_binary_expr(src), src.id_string());
  }

  else if(
    src.id() == ID_smv_EBF || src.id() == ID_smv_ABF ||
    src.id() == ID_smv_EBG || src.id() == ID_smv_ABG)
  {
    return convert_rtctl(
      to_ternary_expr(src),
      std::string(src.id_string(), 4, std::string::npos),
      precedencet::TEMPORAL);
  }

  else if(src.id() == ID_smv_EBU || src.id() == ID_smv_ABU)
  {
    return convert_rtctl(
      to_multi_ary_expr(src),
      std::string(src.id_string(), 4, 1),
      std::string(src.id_string(), 5, std::string::npos),
      precedencet::TEMPORAL);
  }

  else if(src.id() == ID_R)
  {
    // LTL release is "V" in NuSMV
    return convert_binary(to_R_expr(src), "V", precedencet::TEMPORAL);
  }

  else if(src.id() == ID_smv_S || src.id() == ID_smv_T)
  {
    return convert_binary(
      to_binary_expr(src),
      std::string(src.id_string(), 4, std::string::npos),
      precedencet::TEMPORAL);
  }

  else if(src.id() == ID_if)
    return convert_if(to_if_expr(src), precedencet::IF);

  else if(src.id()==ID_symbol)
    return convert_symbol(to_symbol_expr(src));

  else if(src.id()==ID_next_symbol)
    return convert_next_symbol(src);

  else if(src.id()==ID_constant)
    return convert_constant(to_constant_expr(src));

  else if(src.id()==ID_nondet_bool)
    return convert_smv_set(smv_set_exprt{{false_exprt(), true_exprt()}});

  else if(src.id()==ID_cond)
    return convert_cond(src);

  else if(src.id() == ID_concatenation)
  {
    return convert_binary_associative(
      to_binary_expr(src), "::", precedencet::CONCAT);
  }

  else if(src.id() == ID_shl)
  {
    return convert_binary(to_binary_expr(src), "<<", precedencet::SHIFT);
  }

  else if(src.id() == ID_lshr || src.id() == ID_ashr)
  {
    return convert_binary(to_binary_expr(src), ">>", precedencet::SHIFT);
  }

  else if(src.id() == ID_extractbits)
    return convert_extractbits(to_extractbits_expr(src));

  else if(src.id() == ID_smv_bit_selection)
    return convert_smv_bit_selection(to_ternary_expr(src));

  else if(src.id() == ID_smv_extend)
    return convert_function_application("extend", src);

  else if(src.id() == ID_smv_resize)
    return convert_function_application("resize", src);

  else if(src.id() == ID_smv_signed_cast)
    return convert_function_application("signed", src);

  else if(src.id() == ID_smv_unsigned_cast)
    return convert_function_application("unsigned", src);

  else if(src.id() == ID_smv_abs)
    return convert_function_application("abs", src);

  else if(src.id() == ID_smv_bool)
    return convert_function_application("bool", src);

  else if(src.id() == ID_smv_cases)
    return convert_cond(to_smv_cases_expr(src).lower());

  else if(src.id() == ID_smv_count)
    return convert_function_application("count", src);

  else if(src.id() == ID_smv_max)
    return convert_function_application("max", src);

  else if(src.id() == ID_smv_min)
    return convert_function_application("min", src);

  else if(src.id() == ID_smv_toint)
    return convert_function_application("toint", src);

  else if(src.id() == ID_smv_word1)
    return convert_function_application("word1", src);

  else if(src.id() == ID_typecast)
  {
    return convert_typecast(to_typecast_expr(src));
  }

  else if(src.id() == ID_zero_extend)
    return convert_zero_extend(to_zero_extend_expr(src));

  else // no SMV language expression for internal representation
    return convert_norep(src);
}

/*******************************************************************\

Function: expr2smv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2smv(const exprt &expr, const namespacet &ns)
{
  expr2smvt expr2smv{ns};
  return expr2smv.convert(expr);
}

/*******************************************************************\

Function: type2smv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string type2smv(const typet &type, const namespacet &ns)
{
  if(type.id()==ID_bool)
    return "boolean";
  else if(type.id()==ID_array)
  {
    auto &array_type = to_array_type(type);
    auto size_const = to_constant_expr(array_type.size());
    auto size_int = numeric_cast_v<mp_integer>(size_const);
    std::string code = "array ";
    // The index type cannot be any type, but must be a range low..high
    code += "0..";
    code += integer2string(size_int - 1);
    code+=" of ";
    code += type2smv(array_type.element_type(), ns);
    return code;
  }
  else if(type.id() == ID_smv_enumeration)
  {
    auto elements = to_smv_enumeration_type(type).elements();
    std::string code = "{ ";
    bool first=true;
    for(auto &element : elements)
    {
      if(first) first=false; else code+=", ";
      code += id2string(element);
    }
    code+=" }";
    return code;
  }
  else if(type.id()==ID_range)
  {
    return type.get_string(ID_from) + ".." + type.get_string(ID_to);
  }
  else if(type.id() == ID_smv_set)
  {
    return "set";
  }
  else if(type.id() == ID_smv_module_instance)
  {
    auto code = id2string(to_smv_module_instance_type(type).base_name());
    const exprt &e=(exprt &)type;
    if(e.has_operands())
    {
      code+='(';
      bool first=true;
      forall_operands(it, e)
      {
        if(first) first=false; else code+=", ";
        code += expr2smv(*it, ns);
      }
      code+=')';
    }
    return code;
  }
  else if(type.id() == ID_signedbv)
  {
    return "signed word[" + std::to_string(to_signedbv_type(type).width()) +
           ']';
  }
  else if(type.id() == ID_unsignedbv)
  {
    return "unsigned word[" + std::to_string(to_unsignedbv_type(type).width()) +
           ']';
  }
  else
    return "no conversion for " + type.id_string();
}
