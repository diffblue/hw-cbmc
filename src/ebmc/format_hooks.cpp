/*******************************************************************\

Module:

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "format_hooks.h"

#include <util/format_expr.h>

#include <trans-word-level/next_symbol.h>

void format_hooks()
{
  add_format_hook(
    ID_next_symbol,
    [](std::ostream &os, const exprt &expr) -> std::ostream &
    {
      const auto &next_symbol_expr = to_next_symbol_expr(expr);
      os << "next(" << next_symbol_expr.identifier() << ')';
      return os;
    });
}
