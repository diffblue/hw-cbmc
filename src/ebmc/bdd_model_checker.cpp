/*******************************************************************\

Module: BDD-based CTL Model Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bdd_model_checker.h"

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
