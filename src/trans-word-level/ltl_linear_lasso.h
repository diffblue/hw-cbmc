/*******************************************************************\

Module: Linear Encoding of Lasso-Shaped Counterexamples

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TRANS_WORD_LEVEL_LTL_LINEAR_LASSO_H
#define CPROVER_TRANS_WORD_LEVEL_LTL_LINEAR_LASSO_H

#include <util/expr.h>
#include <util/mp_arith.h>

#include <solvers/decision_procedure.h>

/// Returns true iff the given property, which must be in NNF,
/// is supported by \ref ltl_linear_lasso_obligation.
bool ltl_linear_lasso_supported(const exprt &);

/// Encodes the given property, which must be in NNF and supported
/// (see \ref ltl_linear_lasso_supported), over lasso-shaped paths
/// whose loop closes in the last timeframe, following
/// Biere, Heljanko, Junttila, Latvala, Schuppan,
/// "Linear Encodings of Bounded LTL Model Checking", LMCS 2(5), 2006.
///
/// The loop is chosen by the selectors given by
/// \ref lasso_select_symbol. The values of the subformulas in each
/// timeframe are obtained using \p solver.handle(...), which yields
/// an encoding that is linear in the number of timeframes and in the
/// size of the property.
///
/// Returns a condition that must hold for the property to hold on all
/// such paths. This is "no loop is selected, or the property holds in
/// timeframe 0".
exprt ltl_linear_lasso_obligation(
  const exprt &,
  const mp_integer &no_timeframes,
  decision_proceduret &solver);

#endif // CPROVER_TRANS_WORD_LEVEL_LTL_LINEAR_LASSO_H
