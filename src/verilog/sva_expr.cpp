/*******************************************************************\

Module: System Verilog Asssertion Expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "sva_expr.h"

exprt sva_case_exprt::lowering() const
{
  auto &case_items = this->case_items();

  // base case
  if(case_items.empty())
    return true_exprt();

  // remove one case item, then do recursive call
  exprt::operandst disjuncts;
  disjuncts.reserve(case_items.front().patterns().size());

  for(auto &pattern : case_items.front().patterns())
  {
    disjuncts.push_back(equal_exprt{
      typecast_exprt::conditional_cast(case_op(), pattern.type()), pattern});
  }

  sva_case_exprt reduced = *this;
  reduced.case_items().erase(reduced.case_items().begin());

  // rec. call
  auto reduced_rec = reduced.lowering();

  return if_exprt{
    disjunction(disjuncts), case_items.front().result(), reduced_rec};
}
