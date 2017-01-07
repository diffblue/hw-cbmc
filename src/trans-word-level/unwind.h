/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_UNWIND_H
#define CPROVER_TRANS_UNWIND_H

#include <util/std_expr.h>

// word-level

void unwind(
  const transt &trans,
  class messaget &message,
  class decision_proceduret &decision_procedure,
  unsigned no_timeframes,
  const class namespacet &ns,
  bool initial_state=true);

#endif
