/*******************************************************************\

Module: Unwinding the Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_WORD_LEVEL_PROPERTY_WORD_LEVEL_H
#define CPROVER_TRANS_WORD_LEVEL_PROPERTY_WORD_LEVEL_H

#include <util/expr.h>
#include <util/message.h>
#include <util/mp_arith.h>

#include <solvers/decision_procedure.h>

#include <optional>

/// returns a vector of obligation expressions, one per timeframe
exprt::operandst property(
  const exprt &property_expr,
  bool allow_pending_matches,
  message_handlert &,
  std::size_t no_timeframes);

/// As above, but lasso-shaped counterexamples are encoded using
/// the linear encoding (see ltl_linear_lasso.h) when the property is
/// supported by it, which uses \p solver to obtain handles for the
/// values of the subformulas. The resulting obligations require the
/// constraints added by lasso_constraints(...).
exprt::operandst property(
  const exprt &property_expr,
  bool allow_pending_matches,
  message_handlert &,
  std::size_t no_timeframes,
  decision_proceduret &solver);

/// Does the given property require lasso-shaped counterexamples?
bool property_uses_lasso(const exprt &);

/// Does the given property use the linear lasso encoding
/// when given a solver?
bool property_uses_linear_lasso(const exprt &);

/// Returns the obligation of the linear lasso encoding for the given
/// property, which states that the property holds on the lasso
/// selected by the loop selectors, if any, or {} if the property is not
/// supported by the linear encoding. This is used to constrain
/// lasso-shaped counterexamples by assumptions.
std::optional<exprt> property_linear_lasso_constraint(
  const exprt &property_expr,
  std::size_t no_timeframes,
  decision_proceduret &solver);

/// Is the given property supported by word-level unwinding?
bool bmc_supports_property(const exprt &);

#endif
