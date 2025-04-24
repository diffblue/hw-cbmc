/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "expr2smv.h"
#include "expr2smv_class.h"

/*******************************************************************\

Function: expr2smvt::convert_nondet_choice

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2smvt::resultt expr2smvt::convert_nondet_choice(const exprt &src)
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

    if(precedence > op_rec.p)
      dest += '(';
    dest += op_rec.s;
    if(precedence > op_rec.p)
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
    : src.id() == ID_not        ? true
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
  else if(type.id()==ID_integer ||
          type.id()==ID_natural ||
          type.id()==ID_range ||
          type.id()==ID_enumeration)
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
    return convert_binary(src, "+", precedencet::PLUS);

  else if(src.id()==ID_minus)
  {
    if(src.operands().size()<2)
      return convert_norep(src);
    else
      return convert_binary(src, "-", precedencet::PLUS);
  }

  else if(src.id()==ID_unary_minus)
  {
    if(src.operands().size()!=1)
      return convert_norep(src);
    else
      return convert_unary(to_unary_minus_expr(src), "-", precedencet::UMINUS);
  }

  else if(src.id()==ID_index)
    return convert_index(to_index_expr(src), precedencet::INDEX);

  else if(src.id()==ID_mult || src.id()==ID_div)
    return convert_binary(src, src.id_string(), precedencet::MULT);

  else if(src.id() == ID_mod)
    return convert_binary(src, src.id_string(), precedencet::MULT);

  else if(src.id() == ID_smv_setin)
    return convert_binary(src, "in", precedencet::IN);

  else if(src.id() == ID_smv_setnotin)
    return convert_binary(src, "notin", precedencet::IN);

  else if(src.id() == ID_smv_union)
    return convert_binary(src, "union", precedencet::UNION);

  else if(src.id()==ID_lt || src.id()==ID_gt ||
          src.id()==ID_le || src.id()==ID_ge)
    return convert_binary(src, src.id_string(), precedencet::REL);

  else if(src.id()==ID_equal)
  {
    if(src.get_bool(ID_C_smv_iff))
      return convert_binary(src, "<->", precedencet::IFF);
    else
      return convert_binary(src, "=", precedencet::REL);
  }

  else if(src.id()==ID_notequal)
    return convert_binary(src, "!=", precedencet::REL);

  else if(src.id()==ID_not)
    return convert_unary(to_not_expr(src), "!", precedencet::NOT);

  else if(src.id() == ID_and || src.id() == ID_bitand)
    return convert_binary(src, "&", precedencet::AND);

  else if(src.id() == ID_or || src.id() == ID_bitor)
    return convert_binary(src, "|", precedencet::OR);

  else if(src.id() == ID_implies || src.id() == ID_smv_bitimplies)
    return convert_binary(src, "->", precedencet::IMPLIES);

  else if(src.id() == ID_xor || src.id() == ID_bitxor)
    return convert_binary(src, "xor", precedencet::OR);

  else if(src.id() == ID_xnor || src.id() == ID_bitxnor)
  {
    if(src.get_bool(ID_C_smv_iff))
      return convert_binary(src, "<->", precedencet::IFF);
    else
      return convert_binary(src, "xnor", precedencet::OR);
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

  else if(
    src.id() == ID_AU || src.id() == ID_EU || src.id() == ID_AR ||
    src.id() == ID_ER || src.id() == ID_U)
  {
    return convert_binary(
      to_binary_expr(src), src.id_string(), precedencet::TEMPORAL);
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
    return convert_binary(to_binary_expr(src), "V", precedencet::TEMPORAL);
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

  else if(src.id()=="smv_nondet_choice")
    return convert_nondet_choice(src);

  else if(src.id() == ID_constraint_select_one)
    return convert_nondet_choice(src);

  else if(src.id()==ID_nondet_bool)
  {
    exprt nondet_choice_expr("smv_nondet_choice");
    nondet_choice_expr.operands().clear();
    nondet_choice_expr.operands().push_back(false_exprt());
    nondet_choice_expr.operands().push_back(true_exprt());
    return convert_nondet_choice(nondet_choice_expr);
  }

  else if(src.id()==ID_cond)
    return convert_cond(src);

  else if(src.id() == ID_concatenation)
  {
    return convert_binary(to_binary_expr(src), "::", precedencet::CONCAT);
  }

  else if(src.id() == ID_shl)
  {
    return convert_binary(to_binary_expr(src), "<<", precedencet::SHIFT);
  }

  else if(src.id() == ID_lshr || src.id() == ID_ashr)
  {
    return convert_binary(to_binary_expr(src), ">>", precedencet::SHIFT);
  }

  else if(src.id() == ID_smv_extend)
    return convert_function_application("extend", src);

  else if(src.id() == ID_smv_resize)
    return convert_function_application("resize", src);

  else if(src.id() == ID_smv_signed_cast)
    return convert_function_application("signed", src);

  else if(src.id() == ID_smv_unsigned_cast)
    return convert_function_application("unsigned", src);

  else if(src.id() == ID_typecast)
  {
    return convert_rec(to_typecast_expr(src).op());
  }

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
    std::string code = "array ";
    code+="..";
    code+=" of ";
    code += type2smv(to_array_type(type).element_type(), ns);
    return code;
  }
  else if(type.id()==ID_enumeration)
  {
    const irept::subt &elements=to_enumeration_type(type).elements();
    std::string code = "{ ";
    bool first=true;
    for(auto &element : elements)
    {
      if(first) first=false; else code+=", ";
      code += element.id_string();
    }
    code+=" }";
    return code;
  }
  else if(type.id()==ID_range)
  {
    return type.get_string(ID_from) + ".." + type.get_string(ID_to);
  }
  else if(type.id()=="submodule")
  {
    auto code = type.get_string(ID_identifier);
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
