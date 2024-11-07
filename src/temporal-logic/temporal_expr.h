/*******************************************************************\

Module: Temporal Operators

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_EXPR_H
#define CPROVER_TEMPORAL_EXPR_H

#include <util/std_expr.h>

class E_exprt : public binary_predicate_exprt
{
public:
  explicit E_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_E, std::move(op1))
  {
  }
};

static inline const E_exprt &to_E_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_E);
  E_exprt::check(expr);
  return static_cast<const E_exprt &>(expr);
}

static inline E_exprt &to_E_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_E);
  E_exprt::check(expr);
  return static_cast<E_exprt &>(expr);
}

class A_exprt : public binary_predicate_exprt
{
public:
  explicit A_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_A, std::move(op1))
  {
  }
};

static inline const A_exprt &to_A_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_A);
  A_exprt::check(expr);
  return static_cast<const A_exprt &>(expr);
}

static inline A_exprt &to_A_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_A);
  A_exprt::check(expr);
  return static_cast<A_exprt &>(expr);
}

#endif
