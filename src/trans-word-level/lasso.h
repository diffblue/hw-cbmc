/*******************************************************************\

Module: Lasso Constraints

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TRANS_WORD_LEVEL_LASSO_H
#define CPROVER_TRANS_WORD_LEVEL_LASSO_H

#include <util/mp_arith.h>
#include <util/namespace.h>

#include <solvers/decision_procedure.h>

/// Adds a constraint that can be used to determine whether the
/// given state has already been seen earlier in the trace.
void lasso_constraints(
  decision_proceduret &,
  const mp_integer &no_timeframes,
  const namespacet &,
  const irep_idt &module_identifier);

/// Is there a loop from i back to k?
/// Precondition: k<i
symbol_exprt lasso_symbol(const mp_integer &k, const mp_integer &i);

/// Returns true iff the given property requires lasso constraints for BMC.
bool requires_lasso_constraints(const exprt &);

#endif
