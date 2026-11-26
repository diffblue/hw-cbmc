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
#include <trans-netlist/trans_trace.h>

#include <optional>
#include <set>

/// Adds the constraints that define the given lasso symbols, i.e., the
/// symbols obtained from \ref lasso_symbol and \ref lasso_select_symbol
/// that are contained in \p used_lasso_symbols. The states are compared
/// on the state variables and top-level inputs of the module; when
/// given, only on those whose identifiers are in \p relevant_variables.
void lasso_constraints(
  decision_proceduret &,
  const mp_integer &no_timeframes,
  const namespacet &,
  const irep_idt &module_identifier,
  const std::set<irep_idt> &used_lasso_symbols,
  const std::optional<std::set<irep_idt>> &relevant_variables);

/// Is there a loop from i back to k?
/// Precondition: k<i
symbol_exprt lasso_symbol(const mp_integer &k, const mp_integer &i);

/// Loop selector for the linear lasso encoding: the lasso closes at
/// the last timeframe \p last, whose state is equal to the state in
/// timeframe \p j, and the successor of the last timeframe is
/// timeframe j+1. At most one of the selectors for a given \p last
/// is true.
/// Precondition: j<last
symbol_exprt lasso_select_symbol(const mp_integer &j, const mp_integer &last);

/// Returns true iff the given formula uses a lasso symbol
bool uses_lasso_symbol(const exprt::operandst &);

/// Adds the identifiers of the lasso symbols that occur in the given
/// expressions to \p dest
void collect_lasso_symbols(const exprt::operandst &, std::set<irep_idt> &dest);

/// The linear lasso encoding yields counterexamples that comprise all
/// timeframes. This replaces the lasso selected in the given solution
/// by the shortest lasso that describes the same infinite path,
/// i.e., the trace ends with the first state that repeats an
/// earlier state on the same infinite path.
void shorten_lasso_trace(
  trans_tracet &,
  const decision_proceduret &,
  std::size_t no_timeframes);

#endif
