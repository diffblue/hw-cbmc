/*******************************************************************\

Module: BDD-based CTL Model Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EBMC_BDD_MODEL_CHECKER_H
#define CPROVER_EBMC_BDD_MODEL_CHECKER_H

#include <util/expr.h>
#include <util/message.h>

#include <solvers/bdd/miniBDD/miniBDD.h>

#include <functional>
#include <map>
#include <vector>

/// A BDD-based transition system model.
/// Current and next-state variables are paired; inputs have no next-state.
struct bdd_modelt
{
  struct vart
  {
    bool is_input;
    mini_bddt current, next;
  };

  mini_bdd_mgrt &mgr;
  std::vector<vart> vars;
  std::vector<mini_bddt> initial, transition, constraints;
};

/// Result of BDD model checking a single property.
struct bdd_check_resultt
{
  enum class statust
  {
    PROVED,
    REFUTED,
    UNKNOWN
  };
  statust status = statust::UNKNOWN;
  /// Number of backward-reachability iterations (for AG p counterexamples).
  unsigned number_of_timeframes = 0;
};

/// Evaluate a CTL property over a BDD model.
/// Atomic propositions in the property expression must be literal_exprt,
/// and their literal variable numbers index into \p atomic_proposition_bdds.
/// \return the set of states (as a BDD) satisfying the property
mini_bddt bdd_ctl(
  const bdd_modelt &,
  const exprt &property,
  const std::map<unsigned, mini_bddt> &atomic_proposition_bdds,
  message_handlert &);

/// Check a CTL property: does every initial state satisfy it?
bdd_check_resultt bdd_check_ctl(
  const bdd_modelt &,
  const exprt &property,
  const std::map<unsigned, mini_bddt> &atomic_proposition_bdds,
  message_handlert &);

/// Optimized check for AG p properties using backward reachability.
bdd_check_resultt bdd_check_AGp(
  const bdd_modelt &,
  const exprt &property,
  const std::map<unsigned, mini_bddt> &atomic_proposition_bdds,
  message_handlert &);

#endif // CPROVER_EBMC_BDD_MODEL_CHECKER_H
