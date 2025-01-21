/*******************************************************************\

Module: System Verilog Asssertion Expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "sva_expr.h"

#include <util/arith_tools.h>
#include <util/mathematical_types.h>

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

exprt sva_sequence_consecutive_repetition_exprt::lower() const
{
  auto n = numeric_cast_v<mp_integer>(to_constant_expr(rhs()));
  DATA_INVARIANT(n >= 1, "number of repetitions must be at least one");

  exprt result = lhs();

  for(; n >= 2; --n)
  {
    auto cycle_delay =
      sva_cycle_delay_exprt{from_integer(1, integer_typet{}), lhs()};
    result = sva_sequence_concatenation_exprt{
      std::move(result), std::move(cycle_delay)};
  }

  return result;
}
