/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_UNWIND_H
#define CPROVER_TRANS_UNWIND_H

#include <namespace.h>
#include <message.h>
#include <hash_cont.h>
#include <decision_procedure.h>
#include <std_expr.h>

// word-level

void unwind(
  const transt &trans,
  messaget &message,
  decision_proceduret &decision_procedure,
  unsigned no_timeframes,
  const namespacet &ns,
  bool initial_state=true);

#endif
