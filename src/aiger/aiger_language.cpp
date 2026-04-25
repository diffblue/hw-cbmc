/*******************************************************************\

Module: AIGER Language Registration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "aiger_language.h"

#include <util/std_expr.h>

bool aiger_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  if(expr.is_true())
    code = "TRUE";
  else if(expr.is_false())
    code = "FALSE";
  else if(expr.id() == ID_not)
  {
    std::string op_code;
    from_expr(to_not_expr(expr).op(), op_code, ns);
    code = "!" + op_code;
  }
  else if(expr.id() == ID_symbol)
    code = id2string(to_symbol_expr(expr).get_identifier());
  else
    code = expr.pretty();
  return false;
}

bool aiger_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &)
{
  if(type.id() == ID_bool)
    code = "Bool";
  else
    code = type.pretty();
  return false;
}

std::unique_ptr<languaget> new_aiger_language()
{
  return std::make_unique<aiger_languaget>();
}
