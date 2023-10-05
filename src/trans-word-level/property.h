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
  std::size_t no_timeframes,
  const namespacet &);

/// Adds a constraint that can be used to determine whether the
/// given state has already been seen earlier in the trace.
void lasso_constraints(
  decision_proceduret &,
  std::size_t no_timeframes,
  const namespacet &,
  const irep_idt &module_identifier);

symbol_exprt lasso_symbol(std::size_t);

/// Returns true iff the given property requires lasso constraints.
bool requires_lasso_constraints(const exprt &);

#endif
