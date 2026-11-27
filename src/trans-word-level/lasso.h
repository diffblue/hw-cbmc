/*******************************************************************\

Module: Lasso Constraints

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TRANS_WORD_LEVEL_LASSO_H
#define CPROVER_TRANS_WORD_LEVEL_LASSO_H

#include <util/expr.h>
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

/// Adds the lasso constraints for the lasso symbols lasso_symbol(k, i)
/// with from_timeframe <= i < to_timeframe and k < i. Calling this
/// with 0..a and then a..b yields the same constraints as a single
/// call with 0..b, which enables incremental unwinding.
void lasso_constraints(
  decision_proceduret &,
  const mp_integer &from_timeframe,
  const mp_integer &to_timeframe,
  const namespacet &,
  const irep_idt &module_identifier);

/// Is there a loop from i back to k?
/// Precondition: k<i
symbol_exprt lasso_symbol(const mp_integer &k, const mp_integer &i);

/// Returns true iff the given formula uses a lasso symbol
bool uses_lasso_symbol(const exprt::operandst &);

#endif
