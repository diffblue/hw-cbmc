/*******************************************************************\

Module: BTOR2 Language Registration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "btor_language.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

bool btor_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  if(expr.is_true())
    code = "TRUE";
  else if(expr.is_false())
    code = "FALSE";
  else if(expr.is_constant())
  {
    auto &type = expr.type();
    if(type.id() == ID_unsignedbv || type.id() == ID_signedbv)
    {
      auto value = numeric_cast_v<mp_integer>(to_constant_expr(expr));
      code = integer2string(value);
    }
    else
      code = expr.pretty();
  }
  else if(expr.id() == ID_symbol)
    code = id2string(to_symbol_expr(expr).get_identifier());
  else if(expr.id() == ID_not)
  {
    std::string op_code;
    from_expr(to_not_expr(expr).op(), op_code, ns);
    code = "!" + op_code;
  }
  else
    code = expr.pretty();
  return false;
}

bool btor_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &)
{
  if(type.id() == ID_unsignedbv)
    code = "bitvec " + std::to_string(to_unsignedbv_type(type).get_width());
  else
    code = type.pretty();
  return false;
}

std::unique_ptr<languaget> new_btor_language()
{
  return std::make_unique<btor_languaget>();
}
