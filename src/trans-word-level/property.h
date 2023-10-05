/*******************************************************************\

Module: Unwinding the Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_WORD_LEVEL_PROPERTY_WORD_LEVEL_H
#define CPROVER_TRANS_WORD_LEVEL_PROPERTY_WORD_LEVEL_H

#include <util/expr.h>
#include <util/message.h>
#include <util/namespace.h>

#include <solvers/decision_procedure.h>

void property(
  const exprt &property_expr,
  exprt::operandst &prop_handles,
  message_handlert &,
  decision_proceduret &solver,
  unsigned no_timeframes,
  const namespacet &);

#endif
