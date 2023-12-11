/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_WORD_LEVEL_NEXT_STATE_H
#define CPROVER_TRANS_WORD_LEVEL_NEXT_STATE_H

#include <util/std_expr.h>

class next_symbol_exprt : public nullary_exprt
{
public:
  next_symbol_exprt(irep_idt _identifier, typet _type)
    : nullary_exprt(ID_next_symbol, std::move(_type))
  {
    identifier(_identifier);
  }

  explicit next_symbol_exprt(const symbol_exprt &symbol_expr)
    : next_symbol_exprt(symbol_expr.get_identifier(), symbol_expr.type())
  {
  }

  const irep_idt &identifier() const
  {
    return get(ID_identifier);
  }

  void identifier(irep_idt _identifier)
  {
    set(ID_identifier, _identifier);
  }
};

inline const next_symbol_exprt &to_next_symbol_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_next_symbol);
  return static_cast<const next_symbol_exprt &>(expr);
}

inline next_symbol_exprt &to_next_symbol_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_next_symbol);
  return static_cast<next_symbol_exprt &>(expr);
}

#endif // CPROVER_TRANS_WORD_LEVEL_NEXT_STATE_H
