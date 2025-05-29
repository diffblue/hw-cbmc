/*******************************************************************\

Module: Property Instrumentation via Buechi Automata

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_LTL_TO_BUECHI_H
#define CPROVER_EBMC_LTL_TO_BUECHI_H

#include <util/std_expr.h>

struct buechi_transt
{
  symbol_exprt state_symbol;

  exprt init;
  exprt trans;
  exprt liveness_signal;

  buechi_transt(
    symbol_exprt __state_symbol,
    exprt __init,
    exprt __trans,
    exprt __liveness_signal)
    : state_symbol(std::move(__state_symbol)),
      init(std::move(__init)),
      trans(std::move(__trans)),
      liveness_signal(std::move(__liveness_signal))
  {
  }

  void rename_state_symbol(const symbol_exprt &new_state_symbol);
};

class message_handlert;

buechi_transt ltl_to_buechi(const exprt &formula, message_handlert &);

#endif
