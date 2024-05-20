/*******************************************************************\

Module: Liveness Signal

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "live_signal.h"

#include <temporal-logic/temporal_expr.h>
#include <verilog/sva_expr.h>

#include "transition_system.h"

void set_liveness_signal(transition_systemt &transition_system, exprt property)
{
  static const irep_idt identifier = id2string(transition_system.main_symbol->name) + ".$live";

  // add symbol if needed
  if(!transition_system.symbol_table.has_symbol(identifier))
  {
    symbolt live_symbol{
      identifier, bool_typet(), transition_system.main_symbol->mode};

    live_symbol.module = transition_system.main_symbol->module;
    live_symbol.base_name = "$live";

    const auto symbol_expr = live_symbol.symbol_expr();

    auto result = transition_system.symbol_table.insert(std::move(live_symbol));
    CHECK_RETURN(result.second);
  }

  const auto p = [](const exprt &expr) -> exprt {
    if(expr.id() == ID_AF)
      return to_AF_expr(expr).op();
    else if(
      expr.id() == ID_sva_always &&
      to_sva_always_expr(expr).op().id() == ID_sva_s_eventually)
    {
      return to_sva_s_eventually_expr(to_sva_always_expr(expr).op()).op();
    }
    else
      PRECONDITION(false);
  }(property);

  const auto live_symbol_expr = symbol_exprt(identifier, bool_typet());

  auto &trans_expr = transition_system.trans_expr;

  trans_expr.invar() =
    conjunction({trans_expr.invar(), equal_exprt(live_symbol_expr, p)});
}
