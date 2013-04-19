/*******************************************************************\

Module: Replace guards by truth values

Author: Daniel Kroening, Himanshu Jain

\*******************************************************************/

#ifndef CPROVER_INSTANTIATE_GUARDS_H
#define CPROVER_INSTANTIATE_GUARDS_H

#include "predicates.h"
#include "abstract_counterexample.h"

void instantiate_guards_main(
  const predicatest &predicates,
  const abstract_statet &abstract_state,
  exprt &expr,
  std::set<unsigned> &preds_used_to_simplify);

void instantiate_guards_simplify(
  const predicatest &predicates,
  const abstract_statet &abstract_state,
  exprt &expr,
  std::set<unsigned> &preds_used_to_simplify);

#endif
