/*******************************************************************\

Module: LTL Temporal Operators

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGIC_LTL_H
#define CPROVER_TEMPORAL_LOGIC_LTL_H

#include <util/std_expr.h>

class F_exprt : public unary_predicate_exprt
{
public:
  explicit F_exprt(exprt op) : unary_predicate_exprt(ID_F, std::move(op))
  {
  }
};

static inline const F_exprt &to_F_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_F);
  F_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const F_exprt &>(expr);
}

static inline F_exprt &to_F_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_F);
  F_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<F_exprt &>(expr);
}

class G_exprt : public unary_predicate_exprt
{
public:
  explicit G_exprt(exprt op) : unary_predicate_exprt(ID_G, std::move(op))
  {
  }
};

static inline const G_exprt &to_G_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_G);
  G_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const G_exprt &>(expr);
}

static inline G_exprt &to_G_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_G);
  G_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<G_exprt &>(expr);
}

/// standard (strong) LTL until, i.e.,
/// the rhs must become true eventually
class U_exprt : public binary_predicate_exprt
{
public:
  explicit U_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_U, std::move(op1))
  {
  }
};

static inline const U_exprt &to_U_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_U);
  U_exprt::check(expr);
  return static_cast<const U_exprt &>(expr);
}

static inline U_exprt &to_U_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_U);
  U_exprt::check(expr);
  return static_cast<U_exprt &>(expr);
}

/// weak LTL until, i.e.,
/// the rhs is not required to become true eventually
class weak_U_exprt : public binary_predicate_exprt
{
public:
  explicit weak_U_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_weak_U, std::move(op1))
  {
  }
};

static inline const weak_U_exprt &to_weak_U_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_weak_U);
  weak_U_exprt::check(expr);
  return static_cast<const weak_U_exprt &>(expr);
}

static inline weak_U_exprt &to_weak_U_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_weak_U);
  weak_U_exprt::check(expr);
  return static_cast<weak_U_exprt &>(expr);
}

class R_exprt : public binary_predicate_exprt
{
public:
  explicit R_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_R, std::move(op1))
  {
  }
};

static inline const R_exprt &to_R_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_R);
  R_exprt::check(expr);
  return static_cast<const R_exprt &>(expr);
}

static inline R_exprt &to_R_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_R);
  R_exprt::check(expr);
  return static_cast<R_exprt &>(expr);
}

class strong_R_exprt : public binary_predicate_exprt
{
public:
  explicit strong_R_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_strong_R, std::move(op1))
  {
  }
};

static inline const strong_R_exprt &to_strong_R_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_strong_R);
  strong_R_exprt::check(expr);
  return static_cast<const strong_R_exprt &>(expr);
}

static inline strong_R_exprt &to_strong_R_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_strong_R);
  strong_R_exprt::check(expr);
  return static_cast<strong_R_exprt &>(expr);
}

class X_exprt : public unary_predicate_exprt
{
public:
  explicit X_exprt(exprt op) : unary_predicate_exprt(ID_X, std::move(op))
  {
  }
};

static inline const X_exprt &to_X_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_X);
  X_exprt::check(expr);
  return static_cast<const X_exprt &>(expr);
}

static inline X_exprt &to_X_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_X);
  X_exprt::check(expr);
  return static_cast<X_exprt &>(expr);
}

#endif
