/*******************************************************************\

Module: SMV Expressions

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "smv_expr.h"

#include <util/arith_tools.h>
#include <util/mathematical_types.h>

smv_resize_exprt::smv_resize_exprt(exprt __op, std::size_t __size, typet __type)
  : smv_resize_exprt{
      std::move(__op),
      from_integer(__size, natural_typet{}),
      std::move(__type)}
{
}

smv_extend_exprt::smv_extend_exprt(exprt __op, std::size_t __size, typet __type)
  : smv_extend_exprt{
      std::move(__op),
      from_integer(__size, natural_typet{}),
      std::move(__type)}
{
}

cond_exprt smv_cases_exprt::lower() const
{
  auto &cases = this->cases();

  exprt::operandst cond_ops;
  cond_ops.reserve(cases.size() * 2);

  for(auto &case_expr : cases)
  {
    DATA_INVARIANT(
      case_expr.operands().size() == 2, "case expected to have two operands");
    cond_ops.push_back(case_expr.condition());
    cond_ops.push_back(case_expr.value());
  }

  auto cond_expr = cond_exprt{cond_ops, type()};
  cond_expr.add_source_location() = source_location();
  return cond_expr;
}
