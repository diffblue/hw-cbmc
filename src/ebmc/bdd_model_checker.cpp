/*******************************************************************\

Module: BDD-based CTL Model Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bdd_model_checker.h"

#include <util/invariant.h>

#include <unordered_map>
#include <unordered_set>

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

mini_bddt bdd_model_checkert::project_inputs(const mini_bddt &bdd) const
{
  mini_bddt tmp = bdd;

  for(const auto &v : transition_relation.variables)
    if(v.is_input)
      tmp = exists(tmp, v.current.var());

  return tmp;
}

/// Collect the set of BDD variable indices appearing in a BDD.
/// The visited set must be keyed on node numbers, not variable indices:
/// two distinct nodes may carry the same variable but have different
/// subgraphs, and skipping one of them would under-approximate the support.
static void support(
  const mini_bddt &bdd,
  std::unordered_set<unsigned> &visited,
  std::unordered_set<unsigned> &vars)
{
  if(bdd.is_constant())
    return;
  if(!visited.insert(bdd.node_number()).second)
    return; // already visited
  vars.insert(bdd.var());
  support(bdd.low(), visited, vars);
  support(bdd.high(), visited, vars);
}

static std::unordered_set<unsigned> support(const mini_bddt &bdd)
{
  std::unordered_set<unsigned> visited, vars;
  support(bdd, visited, vars);
  return vars;
}

/// Early variable quantification as described in
/// Burch, Clarke, McMillan, Dill, Hwang:
/// "Symbolic Model Checking for Sequential Circuit Verification" (1992).
/// Computes ∃ quantified_vars. (conjuncts[0] & ... & conjuncts[n-1]).
/// Instead of building the monolithic conjunction and then quantifying,
/// we interleave conjunction and quantification: a variable is
/// quantified out immediately after the last conjunct that mentions it
/// has been conjoined. This can reduce intermediate BDD sizes from
/// exponential to polynomial.
mini_bddt bdd_model_checkert::conjoin_and_quantify(
  const std::vector<mini_bddt> &conjuncts,
  const std::unordered_set<unsigned> &quantified_vars) const
{
  PRECONDITION(!conjuncts.empty());

  // For each conjunct, the quantified variables whose last occurrence
  // is in that conjunct. Variables that occur in no conjunct need not
  // be quantified at all.
  std::vector<std::vector<unsigned>> quantify_after(conjuncts.size());

  {
    std::unordered_map<unsigned, std::size_t> last_use;

    for(std::size_t i = 0; i < conjuncts.size(); i++)
      for(auto var : support(conjuncts[i]))
        if(quantified_vars.find(var) != quantified_vars.end())
          last_use[var] = i; // later conjuncts overwrite earlier ones

    for(const auto &[var, i] : last_use)
      quantify_after[i].push_back(var);
  }

  mini_bddt result = conjuncts.front();

  for(std::size_t i = 0; i < conjuncts.size(); i++)
  {
    if(i != 0)
      result = result & conjuncts[i];

    for(auto var : quantify_after[i])
      result = exists(result, var);
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

  // The result is over current-state variables only: all next-state
  // variables and the current-state copies of the inputs are
  // existentially quantified.
  std::unordered_set<unsigned> quantified_vars;
  for(const auto &v : transition_relation.variables)
  {
    quantified_vars.insert(v.next.var());
    if(v.is_input)
      quantified_vars.insert(v.current.var());
  }

  return conjoin_and_quantify(conjuncts, quantified_vars);
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

  return project_inputs(project_next(conjunction));
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
