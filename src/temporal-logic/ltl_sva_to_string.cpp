/*******************************************************************\

Module: Property Instrumentation via Buechi Automata

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "ltl_sva_to_string.h"

#include "temporal_expr.h"

ltl_sva_to_stringt::resultt
ltl_sva_to_stringt::prefix(std::string s, const exprt &expr)
{
  auto op_rec = to_string_rec(to_unary_expr(expr).op());

  auto new_e = to_unary_expr(expr);
  new_e.op() = op_rec.e;

  if(op_rec.p != precedencet::INFIX)
    return resultt{precedencet::PREFIX, s + op_rec.s, new_e};
  else
    return resultt{precedencet::PREFIX, s + '(' + op_rec.s + ')', new_e};
}

ltl_sva_to_stringt::resultt
ltl_sva_to_stringt::infix(std::string s, const exprt &expr)
{
  std::string result;
  bool first = true;
  exprt new_e = expr; // copy

  for(auto &op : new_e.operands())
  {
    if(first)
      first = false;
    else
      result += s;

    auto op_rec = to_string_rec(op);
    op = op_rec.e;

    if(op_rec.p == precedencet::ATOM)
      result += op_rec.s;
    else
      result += '(' + op_rec.s + ')';
  }

  return resultt{precedencet::INFIX, result, new_e};
}

ltl_sva_to_stringt::resultt ltl_sva_to_stringt::to_string_rec(const exprt &expr)
{
  if(expr.id() == ID_F)
  {
    return prefix("F", expr);
  }
  else if(expr.id() == ID_G)
  {
    return prefix("G", expr);
  }
  else if(expr.id() == ID_X)
  {
    return prefix("X", expr);
  }
  else if(expr.id() == ID_U)
  {
    return infix("U", expr);
  }
  else if(expr.id() == ID_weak_U)
  {
    return infix("W", expr);
  }
  else if(expr.id() == ID_R)
  {
    return infix("R", expr);
  }
  else if(expr.id() == ID_strong_R)
  {
    return infix("M", expr);
  }
  else if(expr.id() == ID_and)
  {
    return infix("&", expr);
  }
  else if(expr.id() == ID_or)
  {
    return infix("|", expr);
  }
  else if(expr.id() == ID_xor)
  {
    return infix(" xor ", expr);
  }
  else if(expr.id() == ID_implies)
  {
    return infix("->", expr);
  }
  else if(expr.id() == ID_not)
  {
    return prefix("!", expr);
  }
  else
  {
    auto number = atoms.number(expr);
    std::string s;
    if(number <= 'z' - 'a')
      s = std::string(1, 'a' + number);
    else
      s = "a" + std::to_string(number);

    symbol_exprt new_e{s, expr.type()};

    return resultt{precedencet::ATOM, s, new_e};
  }
}
