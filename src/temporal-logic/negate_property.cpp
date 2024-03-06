/*******************************************************************\

Module: Property Negation

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "negate_property.h"

#include <util/std_expr.h>

#include <verilog/sva_expr.h>

#include "temporal_expr.h"

/*******************************************************************\

Function: negate_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt negate_property(const exprt &expr)
{
  if(expr.id() == ID_and)
  {
    exprt result = expr;
    result.id(ID_or);
    for(auto &op : result.operands())
      op = negate_property(op);
    return result;
  }
  else if(expr.id() == ID_or)
  {
    exprt result = expr;
    result.id(ID_and);
    for(auto &op : result.operands())
      op = negate_property(op);
    return result;
  }
  else if(expr.id() == ID_not)
  {
    return to_not_expr(expr).op();
  }
  else if(expr.id() == ID_implies || expr.id() == ID_sva_overlapped_implication)
  {
    binary_exprt result = to_binary_expr(expr);
    result.id(ID_and);
    result.op1() = negate_property(result.op1());
    return std::move(result);
  }
  else if(expr.id() == ID_AG)
  {
    unary_exprt result = to_AG_expr(expr);
    result.id(ID_EF);
    result.op() = negate_property(result.op());
    return std::move(result);
  }
  else if(expr.id() == ID_sva_always)
  {
    unary_exprt result = to_sva_always_expr(expr);
    result.id(ID_sva_eventually);
    result.op() = negate_property(result.op());
    return std::move(result);
  }
  else if(expr.id() == ID_AF)
  {
    unary_exprt result = to_unary_expr(expr);
    result.id(ID_EG);
    result.op() = negate_property(result.op());
    return std::move(result);
  }
  else if(expr.id() == ID_sva_s_eventually)
  {
    unary_exprt result = to_sva_s_eventually_expr(expr);
    result.id(ID_sva_always);
    result.op() = negate_property(result.op());
    return std::move(result);
  }
  else if(expr.id() == ID_sva_non_overlapped_implication)
  {
    // rewrite using 'next'
    unary_predicate_exprt next(ID_sva_nexttime, to_binary_expr(expr).rhs());
    binary_exprt result = to_binary_expr(expr);
    result.op1() = negate_property(next);
    return std::move(result);
  }
  else if(expr.id() == ID_sva_nexttime)
  {
    unary_exprt result = to_sva_nexttime_expr(expr);
    result.op() = negate_property(result.op());
    return std::move(result);
  }
  else
    return not_exprt(expr);
}
