/*******************************************************************\

Module: BDD-based CTL Model Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bdd_model_checker.h"

#include <set>

bdd_model_checkert::bdd_model_checkert(
  const bdd_transition_relationt &_transition_relation)
  : transition_relation(_transition_relation)
{
}

mini_bddt bdd_model_checkert::current_to_next(const mini_bddt &bdd) const
{
  mini_bddt tmp = bdd;

  for(const auto &v : transition_relation.variables)
    tmp = substitute(tmp, v.current.var(), v.next);

  return tmp;
}

mini_bddt bdd_model_checkert::project_next(const mini_bddt &bdd) const
{
  mini_bddt tmp = bdd;

  for(const auto &v : transition_relation.variables)
    tmp = exists(tmp, v.next.var());

  return tmp;
}

/// Collect the set of BDD variable indices appearing in a BDD.
static void support(const mini_bddt &bdd, std::set<unsigned> &vars)
{
  if(bdd.is_constant())
    return;
  if(!vars.insert(bdd.var()).second)
    return; // already visited
  support(bdd.low(), vars);
  support(bdd.high(), vars);
}

/// Early variable quantification as described in
/// Burch, Clarke, McMillan, Dill, Hwang:
/// "Symbolic Model Checking for Sequential Circuit Verification" (1992).
/// Instead of building the monolithic conjunction of all transition
/// conjuncts and then quantifying out next-state variables, we
/// interleave conjunction and quantification: after conjoining each
/// partition, we immediately quantify out next-state variables that
/// do not appear in any remaining partition.
mini_bddt bdd_model_checkert::project_next_early(
  const std::vector<mini_bddt> &conjuncts) const
{
  // Collect the set of next-state variable indices.
  std::set<unsigned> next_vars;
  for(const auto &v : transition_relation.variables)
    next_vars.insert(v.next.var());

  // Compute the support of each conjunct.
  std::vector<std::set<unsigned>> conjunct_supports(conjuncts.size());
  for(std::size_t i = 0; i < conjuncts.size(); i++)
    support(conjuncts[i], conjunct_supports[i]);

  mini_bddt result = conjuncts.front();

  for(std::size_t i = 1; i < conjuncts.size(); i++)
  {
    result = result & conjuncts[i];

    // Quantify out next-state variables that don't appear in any
    // remaining conjunct, and keep only those that are still needed.
    std::set<unsigned> remaining_next_vars;
    for(auto var : next_vars)
    {
      bool needed_later = false;
      for(std::size_t j = i + 1; j < conjuncts.size(); j++)
      {
        if(conjunct_supports[j].count(var))
        {
          needed_later = true;
          break;
        }
      }
      if(needed_later)
        remaining_next_vars.insert(var);
      else
        result = exists(result, var);
    }
    next_vars = std::move(remaining_next_vars);
  }

  return result;
}

mini_bddt bdd_model_checkert::fixedpoint(
  std::function<mini_bddt(mini_bddt)> tau,
  mini_bddt x)
{
  while(true)
  {
    mini_bddt image = tau(x);

    if((image == x).is_true())
      return x;

    x = image;
  }
}

mini_bddt bdd_model_checkert::EX(mini_bddt f)
{
  for(const auto &c : transition_relation.constraint_conjuncts)
    f = f & c;

  mini_bddt p_next = current_to_next(f);

  // Collect all conjuncts for early quantification.
  std::vector<mini_bddt> conjuncts;
  conjuncts.reserve(
    1 + transition_relation.transition_conjuncts.size() +
    transition_relation.constraint_conjuncts.size());

  conjuncts.push_back(p_next);

  for(const auto &t : transition_relation.transition_conjuncts)
    conjuncts.push_back(t);

  for(const auto &c : transition_relation.constraint_conjuncts)
    conjuncts.push_back(c);

  return project_next_early(conjuncts);
}

mini_bddt bdd_model_checkert::EX_monolithic(mini_bddt f)
{
  for(const auto &c : transition_relation.constraint_conjuncts)
    f = f & c;

  mini_bddt p_next = current_to_next(f);

  mini_bddt conjunction = p_next;

  for(const auto &t : transition_relation.transition_conjuncts)
    conjunction = conjunction & t;

  for(const auto &c : transition_relation.constraint_conjuncts)
    conjunction = conjunction & c;

  return project_next(conjunction);
}

mini_bddt bdd_model_checkert::EF(mini_bddt f)
{
  return fixedpoint([this](mini_bddt x) { return x | EX(x); }, f);
}

mini_bddt bdd_model_checkert::EG(mini_bddt f)
{
  return fixedpoint([this](mini_bddt x) { return x & EX(x); }, f);
}

mini_bddt bdd_model_checkert::EU(mini_bddt f1, mini_bddt f2)
{
  return fixedpoint(
    [this, f1, f2](mini_bddt x) { return x | f2 | (f1 & EX(x)); }, f2);
}

mini_bddt bdd_model_checkert::AU(mini_bddt f1, mini_bddt f2)
{
  return fixedpoint(
    [this, f1, f2](mini_bddt x) { return x | f2 | (f1 & AX(x)); }, f2);
}
