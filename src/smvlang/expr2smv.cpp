/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstring>

#include <util/lispexpr.h>
#include <util/lispirep.h>
#include <util/std_expr.h>

#include "expr2smv.h"

class expr2smvt
{
public:
  bool convert_nondet_choice(const exprt &src, std::string &dest, unsigned precedence);

  bool convert_binary(const exprt &src, std::string &dest, const std::string &symbol, unsigned precedence);

  bool convert_unary(
    const unary_exprt &,
    std::string &dest,
    const std::string &symbol,
    unsigned precedence);

  bool
  convert_index(const index_exprt &, std::string &dest, unsigned precedence);

  bool convert(const exprt &src, std::string &dest, unsigned &precedence);

  bool convert(const exprt &src, std::string &dest);

  bool convert_symbol(const exprt &src, std::string &dest, unsigned &precedence);

  bool convert_next_symbol(const exprt &src, std::string &dest, unsigned &precedence);

  bool convert_constant(const exprt &src, std::string &dest, unsigned &precedence);

  bool convert_cond(const exprt &src, std::string &dest);

  bool convert_norep(const exprt &src, std::string &dest, unsigned &precedence);

  bool convert(const typet &src, std::string &dest);
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

 SMV Operator Precedences:

 1 %left  COMMA
 2 %right IMPLIES
 3 %left  IFF
 4 %left  OR XOR XNOR
 5 %left  AND
 6 %left  NOT
 7 %left  EX AX EF AF EG AG EE AA SINCE UNTIL TRIGGERED RELEASES EBF EBG ABF ABG BUNTIL MMIN MMAX
 8 %left  OP_NEXT OP_GLOBAL OP_FUTURE
 9 %left  OP_PREC OP_NOTPRECNOT OP_HISTORICAL OP_ONCE
10 %left  APATH EPATH
11 %left  EQUAL NOTEQUAL LT GT LE GE
12 %left  UNION
13 %left  SETIN
14 %left  MOD
15 %left  PLUS MINUS
16 %left  TIMES DIVIDE
17 %left  UMINUS
18 %left  NEXT SMALLINIT
19 %left  DOT
20        [ ]
21 = max

*/

#define SMV_MAX_PRECEDENCE 21

/*******************************************************************\

Function: expr2smvt::convert_nondet_choice

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert_nondet_choice(
  const exprt &src,
  std::string &dest,
  unsigned precedence)
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
  unsigned precedence)
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
    unsigned p;

    if(convert(*it, op, p)) return true;

    if(precedence>p) dest+='(';
    dest+=op;
    if(precedence>p) dest+=')';
  }

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
  unsigned precedence)
{
  std::string op;
  unsigned p;

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
  unsigned precedence)
{
  std::string op;
  unsigned p;

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

Function: expr2smvt::convert_norep

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smvt::convert_norep(
  const exprt &src,
  std::string &dest,
  unsigned &precedence)
{
  precedence=SMV_MAX_PRECEDENCE;
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
  const exprt &src,
  std::string &dest,
  unsigned &precedence)
{
  precedence=SMV_MAX_PRECEDENCE;
  dest=src.get_string(ID_identifier);
 
  if(strncmp(dest.c_str(), "smv::", 5)==0)
    dest.erase(0, 5);

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
  unsigned &precedence)
{
  std::string tmp;
  convert_symbol(src, tmp, precedence);

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
  const exprt &src,
  std::string &dest,
  unsigned &precedence)
{
  precedence=SMV_MAX_PRECEDENCE;

  const typet &type=src.type();
  const std::string &value=src.get_string(ID_value);

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
    dest=value;
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
  unsigned &precedence)
{
  precedence=SMV_MAX_PRECEDENCE;

  if(src.id()==ID_plus)
    return convert_binary(src, dest, "+", precedence=15);

  else if(src.id()==ID_minus)
  {
    if(src.operands().size()<2)
      return convert_norep(src, dest, precedence);
    else     
      return convert_binary(src, dest, "-", precedence=15);
  }

  else if(src.id()==ID_unary_minus)
  {
    if(src.operands().size()!=1)
      return convert_norep(src, dest, precedence);
    else
      return convert_unary(
        to_unary_minus_expr(src), dest, "-", precedence = 17);
  }

  else if(src.id()==ID_index)
    return convert_index(to_index_expr(src), dest, precedence = 20);

  else if(src.id()==ID_mult || src.id()==ID_div)
    return convert_binary(src, dest, src.id_string(), precedence=16);

  else if(src.id()==ID_lt || src.id()==ID_gt ||
          src.id()==ID_le || src.id()==ID_ge)
    return convert_binary(src, dest, src.id_string(), precedence=11);

  else if(src.id()==ID_equal)
    return convert_binary(src, dest, "=", precedence=11);

  else if(src.id()==ID_notequal)
    return convert_binary(src, dest, "!=", precedence=11);

  else if(src.id()==ID_not)
    return convert_unary(to_not_expr(src), dest, "!", precedence = 6);

  else if(src.id()==ID_and)
    return convert_binary(src, dest, "&", precedence=5);

  else if(src.id()==ID_or)
    return convert_binary(src, dest, "|", precedence=4);

  else if(src.id()==ID_implies)
    return convert_binary(src, dest, "->", precedence=2);

  else if(src.id()==ID_iff)
    return convert_binary(src, dest, "<->", precedence=3);

  else if(src.id()==ID_AG || src.id()==ID_EG ||
          src.id()==ID_AX || src.id()==ID_EX)
    return convert_unary(
      to_unary_expr(src), dest, src.id_string() + " ", precedence = 7);

  else if(src.id()==ID_symbol)
    return convert_symbol(src, dest, precedence);

  else if(src.id()==ID_next_symbol)
    return convert_next_symbol(src, dest, precedence);

  else if(src.id()==ID_constant)
    return convert_constant(src, dest, precedence);

  else if(src.id()=="smv_nondet_choice")
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
  unsigned precedence;
  return convert(src, dest, precedence);
}

/*******************************************************************\

Function: expr2smv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool expr2smv(const exprt &expr, std::string &code)
{
  expr2smvt expr2smv;
  return expr2smv.convert(expr, code);
}

/*******************************************************************\

Function: type2smv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool type2smv(const typet &type, std::string &code)
{
  if(type.id()==ID_bool)
    code="boolean";
  else if(type.id()==ID_array)
  {
    std::string tmp;
    if(type2smv(to_array_type(type).subtype(), tmp))
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
        expr2smv(*it, tmp);
        code+=tmp;
      }
      code+=')';
    }
  }
  else
    return true;

  return false;
}
