/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "expr2smv.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/lispexpr.h>
#include <util/lispirep.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol.h>

class expr2smvt
{
public:
  explicit expr2smvt(const namespacet &__ns) : ns(__ns)
  {
  }

protected:
  // In NuSMV 2.6., ! (not)  has a high precedence (above ::), whereas
  // in the CMU SMV implementation it has the same as other boolean operators.
  // We use the CMU SMV precedence for !.
  // Like CMU SMV, we give the same precedence to -> and <->, to avoid ambiguity.
  // Note that the precedence of mod in the CMU SMV differs from NuSMV's.
  // We use NuSMV's.
  enum class precedencet
  {
    MAX = 16,
    INDEX = 15,   // [ ] , [ : ]
    CONCAT = 14,  // ::
    UMINUS = 13,  // - (unary minus)
    MULT = 12,    // * / mod
    PLUS = 11,    // + -
    SHIFT = 10,   // << >>
    UNION = 9,    // union
    IN = 8,       // in
    REL = 7,      // = != < > <= >=
    TEMPORAL = 6, // AX, AF, etc.
    NOT = 5,      // !
    AND = 4,      // &
    OR = 3,       // | xor xnor
    IF = 2,       // (• ? • : •)
    IFF = 1,      // <->
    IMPLIES = 1   // ->
  };

  /*
   From http://www.cs.cmu.edu/~modelcheck/smv/smvmanual.ps

  The order of precedence from high to low is
    * /
    + -
    mod
    = != < > <= >=
    !
    &
    |
    -> <->
  */

public:
  bool convert_nondet_choice(
    const exprt &src,
    std::string &dest,
    precedencet precedence);

  bool convert_binary(
    const exprt &src,
    std::string &dest,
    const std::string &symbol,
    precedencet precedence);

  bool convert_rtctl(
    const ternary_exprt &src,
    std::string &dest,
    const std::string &symbol,
    precedencet precedence);

  bool convert_rtctl(
    const multi_ary_exprt &src,
    std::string &dest,
    const std::string &symbol1,
    const std::string &symbol2,
    precedencet precedence);

  bool convert_unary(
    const unary_exprt &,
    std::string &dest,
    const std::string &symbol,
    precedencet precedence);

  bool
  convert_index(const index_exprt &, std::string &dest, precedencet precedence);

  bool convert(const exprt &src, std::string &dest, precedencet &precedence);

  bool convert_if(const if_exprt &, std::string &dest, precedencet precedence);

  bool convert(const exprt &src, std::string &dest);

  bool convert_symbol(
    const symbol_exprt &,
    std::string &dest,
    precedencet &precedence);

  bool convert_next_symbol(
    const exprt &src,
    std::string &dest,
    precedencet &precedence);

  bool convert_constant(
    const constant_exprt &,
    std::string &dest,
    precedencet &precedence);

  bool convert_cond(const exprt &src, std::string &dest);

  bool
  convert_norep(const exprt &src, std::string &dest, precedencet &precedence);

  bool convert(const typet &src, std::string &dest);

protected:
  const namespacet &ns;
};

/*******************************************************************\

Function: expr2smvt::convert_nondet_choice

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert_nondet_choice(
  const exprt &src,
  std::string &dest,
  precedencet precedence)
{
  dest="{ ";

  bool first=true;

  forall_operands(it, src)
  {
    if(first)
      first=false;
    else
      dest+=", ";

    std::string tmp;
    if(convert(*it, tmp)) return true;
    dest+=tmp;
  }

  dest+=" }";
  return false;
}

/*******************************************************************\

Function: expr2smvt::convert_cond

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert_cond(
  const exprt &src,
  std::string &dest)
{
  dest="case ";

  bool condition=true;

  forall_operands(it, src)
  {
    std::string tmp;
    if(convert(*it, tmp)) return true;
    dest+=tmp;

    if(condition)
      dest+=": ";
    else
      dest+="; ";
    
    condition=!condition;
  }

  dest+="esac";
  return false;
}

/*******************************************************************\

Function: expr2smvt::convert_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert_binary(
  const exprt &src,
  std::string &dest,
  const std::string &symbol,
  precedencet precedence)
{
  if(src.operands().size()<2)
    return convert_norep(src, dest, precedence);

  bool first=true;

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

    std::string op;
    precedencet p;

    if(convert(*it, op, p)) return true;

    if(precedence>p) dest+='(';
    dest+=op;
    if(precedence>p) dest+=')';
  }

  return false;
}

/*******************************************************************\

Function: expr2smvt::convert_rtctl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert_rtctl(
  const ternary_exprt &src,
  std::string &dest,
  const std::string &symbol,
  precedencet precedence)
{
  std::string op0, op1, op2;
  convert(src.op0(), op0);
  convert(src.op1(), op1);
  convert(src.op2(), op2);
  dest = symbol + ' ' + op0 + ".." + op1 + ' ' + op2;
  return false;
}

/*******************************************************************\

Function: expr2smvt::convert_rtctl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert_rtctl(
  const multi_ary_exprt &src,
  std::string &dest,
  const std::string &symbol1,
  const std::string &symbol2,
  precedencet precedence)
{
  std::string op0, op1, op2, op3;
  convert(src.op0(), op0);
  convert(src.op1(), op1);
  convert(src.op2(), op2);
  convert(src.op3(), op3);
  dest = symbol1 + '[' + op0 + ' ' + symbol2 + ' ' + op1 + ".." + op2 + ' ' +
         op3 + ']';
  return false;
}

/*******************************************************************\

Function: expr2smvt::convert_unary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert_unary(
  const unary_exprt &src,
  std::string &dest,
  const std::string &symbol,
  precedencet precedence)
{
  std::string op;
  precedencet p;

  if(convert(src.op(), op, p))
    return true;

  dest+=symbol;
  if(precedence>p) dest+='(';
  dest+=op;
  if(precedence>p) dest+=')';

  return false;
}

/*******************************************************************\

Function: expr2smvt::convert_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert_index(
  const index_exprt &src,
  std::string &dest,
  precedencet precedence)
{
  std::string op;
  precedencet p;

  if(convert(src.op0(), op, p)) return true;

  if(precedence>p) dest+='(';
  dest+=op;
  if(precedence>p) dest+=')';

  if(convert(src.op1(), op, p)) return true;

  dest+='[';
  dest+=op;
  dest+=']';

  return false;
}

/*******************************************************************\

Function: expr2smvt::convert_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert_if(
  const if_exprt &src,
  std::string &dest,
  precedencet precedence)
{
  std::string op;
  precedencet p;

  if(convert(src.cond(), op, p))
    return true;

  if(precedence >= p)
    dest += '(';
  dest += op;
  if(precedence >= p)
    dest += ')';
  dest += '?';

  if(convert(src.true_case(), op, p))
    return true;

  dest += op;
  dest += ':';

  if(convert(src.false_case(), op, p))
    return true;

  if(precedence > p)
    dest += '(';
  dest += op;
  if(precedence > p)
    dest += ')';

  return false;
}

/*******************************************************************\

Function: expr2smvt::convert_norep

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert_norep(
  const exprt &src,
  std::string &dest,
  precedencet &precedence)
{
  precedence = precedencet::MAX;
  dest=src.pretty();
  return false;
}

/*******************************************************************\

Function: expr2smvt::convert_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert_symbol(
  const symbol_exprt &src,
  std::string &dest,
  precedencet &precedence)
{
  precedence = precedencet::MAX;

  auto &symbol = ns.lookup(src);

  dest = id2string(symbol.display_name());

  return false;
}

/*******************************************************************\

Function: expr2smvt::convert_next_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert_next_symbol(
  const exprt &src,
  std::string &dest,
  precedencet &precedence)
{
  std::string tmp;
  convert_symbol(
    symbol_exprt{src.get(ID_identifier), src.type()}, tmp, precedence);

  dest="next("+tmp+")";

  return false;
}

/*******************************************************************\

Function: expr2smvt::convert_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert_constant(
  const constant_exprt &src,
  std::string &dest,
  precedencet &precedence)
{
  precedence = precedencet::MAX;

  const typet &type = src.type();

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
    return convert_norep(src, dest, precedence);

  return false;
}

/*******************************************************************\

Function: expr2smvt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert(
  const exprt &src,
  std::string &dest,
  precedencet &precedence)
{
  precedence = precedencet::MAX;

  if(src.id()==ID_plus)
    return convert_binary(src, dest, "+", precedence = precedencet::PLUS);

  else if(src.id()==ID_minus)
  {
    if(src.operands().size()<2)
      return convert_norep(src, dest, precedence);
    else
      return convert_binary(src, dest, "-", precedence = precedencet::PLUS);
  }

  else if(src.id()==ID_unary_minus)
  {
    if(src.operands().size()!=1)
      return convert_norep(src, dest, precedence);
    else
      return convert_unary(
        to_unary_minus_expr(src), dest, "-", precedence = precedencet::UMINUS);
  }

  else if(src.id()==ID_index)
    return convert_index(
      to_index_expr(src), dest, precedence = precedencet::INDEX);

  else if(src.id()==ID_mult || src.id()==ID_div)
    return convert_binary(
      src, dest, src.id_string(), precedence = precedencet::MULT);

  else if(src.id() == ID_smv_setin)
    return convert_binary(src, dest, "in", precedence = precedencet::IN);

  else if(src.id() == ID_smv_setnotin)
    return convert_binary(src, dest, "notin", precedence = precedencet::IN);

  else if(src.id() == ID_smv_union)
    return convert_binary(src, dest, "union", precedence = precedencet::UNION);

  else if(src.id()==ID_lt || src.id()==ID_gt ||
          src.id()==ID_le || src.id()==ID_ge)
    return convert_binary(
      src, dest, src.id_string(), precedence = precedencet::REL);

  else if(src.id()==ID_equal)
  {
    if(src.get_bool(ID_C_smv_iff))
      return convert_binary(src, dest, "<->", precedence = precedencet::IFF);
    else
      return convert_binary(src, dest, "=", precedence = precedencet::REL);
  }

  else if(src.id()==ID_notequal)
    return convert_binary(src, dest, "!=", precedence = precedencet::REL);

  else if(src.id()==ID_not)
    return convert_unary(
      to_not_expr(src), dest, "!", precedence = precedencet::NOT);

  else if(src.id() == ID_and || src.id() == ID_bitand)
    return convert_binary(src, dest, "&", precedence = precedencet::AND);

  else if(src.id() == ID_or || src.id() == ID_bitor)
    return convert_binary(src, dest, "|", precedence = precedencet::OR);

  else if(src.id() == ID_implies || src.id() == ID_smv_bitimplies)
    return convert_binary(src, dest, "->", precedence = precedencet::IMPLIES);

  else if(src.id() == ID_xor || src.id() == ID_bitxor)
    return convert_binary(src, dest, "xor", precedence = precedencet::OR);

  else if(src.id() == ID_xnor || src.id() == ID_bitxnor)
  {
    if(src.get_bool(ID_C_smv_iff))
      return convert_binary(src, dest, "<->", precedence = precedencet::IFF);
    else
      return convert_binary(src, dest, "xnor", precedence = precedencet::OR);
  }

  else if(
    src.id() == ID_AG || src.id() == ID_EG || src.id() == ID_AF ||
    src.id() == ID_EF || src.id() == ID_AX || src.id() == ID_EX ||
    src.id() == ID_G || src.id() == ID_F || src.id() == ID_X)
  {
    return convert_unary(
      to_unary_expr(src),
      dest,
      src.id_string() + " ",
      precedence = precedencet::TEMPORAL);
  }

  else if(
    src.id() == ID_smv_H || src.id() == ID_smv_O || src.id() == ID_smv_Y ||
    src.id() == ID_smv_Z)
  {
    return convert_unary(
      to_unary_expr(src),
      dest,
      std::string(src.id_string(), 4, std::string::npos) + " ",
      precedence = precedencet::TEMPORAL);
  }

  else if(src.id() == ID_smv_bounded_H || src.id() == ID_smv_bounded_O)
  {
    return convert_unary(
      to_unary_expr(src),
      dest,
      std::string(src.id_string(), 12, std::string::npos) + " ",
      precedence = precedencet::TEMPORAL);
  }

  else if(
    src.id() == ID_AU || src.id() == ID_EU || src.id() == ID_AR ||
    src.id() == ID_ER || src.id() == ID_U)
  {
    return convert_binary(
      to_binary_expr(src),
      dest,
      src.id_string(),
      precedence = precedencet::TEMPORAL);
  }

  else if(
    src.id() == ID_smv_EBF || src.id() == ID_smv_ABF ||
    src.id() == ID_smv_EBG || src.id() == ID_smv_ABG)
  {
    return convert_rtctl(
      to_ternary_expr(src),
      dest,
      std::string(src.id_string(), 4, std::string::npos),
      precedence = precedencet::TEMPORAL);
  }

  else if(src.id() == ID_smv_EBU || src.id() == ID_smv_ABU)
  {
    return convert_rtctl(
      to_multi_ary_expr(src),
      dest,
      std::string(src.id_string(), 4, 1),
      std::string(src.id_string(), 5, std::string::npos),
      precedence = precedencet::TEMPORAL);
  }

  else if(src.id() == ID_R)
  {
    // LTL release is "V" in NuSMV
    return convert_binary(
      to_binary_expr(src), dest, "V", precedence = precedencet::TEMPORAL);
  }

  else if(src.id() == ID_smv_S || src.id() == ID_smv_T)
  {
    return convert_binary(
      to_binary_expr(src),
      dest,
      std::string(src.id_string(), 4, std::string::npos),
      precedence = precedencet::TEMPORAL);
  }

  else if(src.id() == ID_if)
    return convert_if(to_if_expr(src), dest, precedencet::IF);

  else if(src.id()==ID_symbol)
    return convert_symbol(to_symbol_expr(src), dest, precedence);

  else if(src.id()==ID_next_symbol)
    return convert_next_symbol(src, dest, precedence);

  else if(src.id()==ID_constant)
    return convert_constant(to_constant_expr(src), dest, precedence);

  else if(src.id()=="smv_nondet_choice")
    return convert_nondet_choice(src, dest, precedence);

  else if(src.id() == ID_constraint_select_one)
    return convert_nondet_choice(src, dest, precedence);

  else if(src.id()==ID_nondet_bool)
  {
    exprt nondet_choice_expr("smv_nondet_choice");
    nondet_choice_expr.operands().clear();
    nondet_choice_expr.operands().push_back(false_exprt());
    nondet_choice_expr.operands().push_back(true_exprt());
    return convert_nondet_choice(nondet_choice_expr, dest, precedence);
  }

  else if(src.id()==ID_cond)
    return convert_cond(src, dest);

  else if(src.id() == ID_concatenation)
  {
    return convert_binary(
      to_binary_expr(src), dest, "::", precedence = precedencet::CONCAT);
  }

  else if(src.id() == ID_shl)
  {
    return convert_binary(
      to_binary_expr(src), dest, "<<", precedence = precedencet::SHIFT);
  }

  else if(src.id() == ID_lshr || src.id() == ID_ashr)
  {
    return convert_binary(
      to_binary_expr(src), dest, ">>", precedence = precedencet::SHIFT);
  }

  else // no SMV language expression for internal representation 
    return convert_norep(src, dest, precedence);

  return false;
}

/*******************************************************************\

Function: expr2smvt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert(const exprt &src, std::string &dest)
{
  precedencet precedence;
  return convert(src, dest, precedence);
}

/*******************************************************************\

Function: expr2smv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smv(const exprt &expr, std::string &code, const namespacet &ns)
{
  expr2smvt expr2smv(ns);
  return expr2smv.convert(expr, code);
}

/*******************************************************************\

Function: type2smv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool type2smv(const typet &type, std::string &code, const namespacet &ns)
{
  if(type.id()==ID_bool)
    code="boolean";
  else if(type.id()==ID_array)
  {
    std::string tmp;
    if(type2smv(to_array_type(type).element_type(), tmp, ns))
      return true;
    code="array ";
    code+="..";
    code+=" of ";
    code+=tmp;
  }
  else if(type.id()==ID_enumeration)
  {
    const irept::subt &elements=to_enumeration_type(type).elements();
    code="{ ";
    bool first=true;
    for(auto &element : elements)
    {
      if(first) first=false; else code+=", ";
      code += element.id_string();
    }
    code+=" }";
  }
  else if(type.id()==ID_range)
  {
    code=type.get_string(ID_from)+".."+type.get_string(ID_to);
  }
  else if(type.id()=="submodule")
  {
    code=type.get_string(ID_identifier);
    const exprt &e=(exprt &)type;
    if(e.has_operands())
    {
      code+='(';
      bool first=true;
      forall_operands(it, e)
      {
        if(first) first=false; else code+=", ";
        std::string tmp;
        expr2smv(*it, tmp, ns);
        code+=tmp;
      }
      code+=')';
    }
  }
  else if(type.id() == ID_signedbv)
  {
    code =
      "signed word[" + std::to_string(to_signedbv_type(type).width()) + ']';
  }
  else if(type.id() == ID_unsignedbv)
  {
    code =
      "unsigned word[" + std::to_string(to_unsignedbv_type(type).width()) + ']';
  }
  else
    return true;

  return false;
}
