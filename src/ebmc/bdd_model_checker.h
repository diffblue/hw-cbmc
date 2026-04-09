/*******************************************************************\

Module: BDD-based CTL Model Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EBMC_BDD_MODEL_CHECKER_H
#define CPROVER_EBMC_BDD_MODEL_CHECKER_H

#include <solvers/bdd/miniBDD/miniBDD.h>

#include <functional>
#include <vector>

/// Represents a transition relation for BDD-based model checking.
/// Contains the current/next BDD variable pairs and the conjuncts
/// that define the transition relation and state constraints.
struct bdd_transition_relationt
{
  struct variable_pairt
  {
    mini_bddt current;
    mini_bddt next;
  };

  std::vector<variable_pairt> variables;
  std::vector<mini_bddt> transition_conjuncts;
  std::vector<mini_bddt> constraint_conjuncts;
};

/// BDD-based CTL model checking.
/// Provides functions for each CTL operator, computing the set of
/// states (as a BDD) that satisfies the given formula.
class bdd_model_checkert
{
public:
  explicit bdd_model_checkert(const bdd_transition_relationt &);

  // CTL operators
  mini_bddt EX(mini_bddt);
  mini_bddt EX_monolithic(mini_bddt);
  mini_bddt EF(mini_bddt);
  mini_bddt EG(mini_bddt);
  mini_bddt EU(mini_bddt, mini_bddt);
  mini_bddt AU(mini_bddt, mini_bddt);

  // clang-format off
  mini_bddt AX(mini_bddt f) { return !EX(!f); }
  mini_bddt AF(mini_bddt f) { return !EG(!f); }
  mini_bddt AG(mini_bddt f) { return !EF(!f); }
  mini_bddt ER(mini_bddt f1, mini_bddt f2) { return !AU(!f1, !f2); }
  mini_bddt AR(mini_bddt f1, mini_bddt f2) { return !EU(!f1, !f2); }
  // clang-format on

protected:
  const bdd_transition_relationt &transition_relation;

  mini_bddt current_to_next(const mini_bddt &) const;
  mini_bddt project_next(const mini_bddt &) const;
  mini_bddt project_next_early(const std::vector<mini_bddt> &) const;
  mini_bddt fixedpoint(std::function<mini_bddt(mini_bddt)>, mini_bddt);
};

#endif // CPROVER_EBMC_BDD_MODEL_CHECKER_H
