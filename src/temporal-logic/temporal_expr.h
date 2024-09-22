/*******************************************************************\

Module: Temporal Operators

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_EXPR_H
#define CPROVER_TEMPORAL_EXPR_H

#include <util/std_expr.h>

class AG_exprt : public unary_predicate_exprt
{
public:
  explicit AG_exprt(exprt op) : unary_predicate_exprt(ID_AG, std::move(op))
  {
  }
};

static inline const AG_exprt &to_AG_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_AG);
  AG_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const AG_exprt &>(expr);
}

static inline AG_exprt &to_AG_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_AG);
  AG_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<AG_exprt &>(expr);
}

class AF_exprt : public unary_predicate_exprt
{
public:
  explicit AF_exprt(exprt op) : unary_predicate_exprt(ID_AF, std::move(op))
  {
  }
};

static inline const AF_exprt &to_AF_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_AF);
  AF_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const AF_exprt &>(expr);
}

static inline AF_exprt &to_AF_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_AF);
  AF_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<AF_exprt &>(expr);
}

class EG_exprt : public unary_predicate_exprt
{
public:
  explicit EG_exprt(exprt op) : unary_predicate_exprt(ID_EG, std::move(op))
  {
  }
};

static inline const EG_exprt &to_EG_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_EG);
  EG_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const EG_exprt &>(expr);
}

static inline EG_exprt &to_EG_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_EG);
  EG_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<EG_exprt &>(expr);
}

class EF_exprt : public unary_predicate_exprt
{
public:
  explicit EF_exprt(exprt op) : unary_predicate_exprt(ID_EF, std::move(op))
  {
  }
};

static inline const EF_exprt &to_EF_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_EF);
  EF_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const EF_exprt &>(expr);
}

static inline EF_exprt &to_EF_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_EF);
  EF_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<EF_exprt &>(expr);
}

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

class EU_exprt : public binary_predicate_exprt
{
public:
  explicit EU_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_EU, std::move(op1))
  {
  }
};

static inline const EU_exprt &to_EU_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_EU);
  EU_exprt::check(expr);
  return static_cast<const EU_exprt &>(expr);
}

static inline EU_exprt &to_EU_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_EU);
  EU_exprt::check(expr);
  return static_cast<EU_exprt &>(expr);
}

class AU_exprt : public binary_predicate_exprt
{
public:
  explicit AU_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_AU, std::move(op1))
  {
  }
};

static inline const AU_exprt &to_AU_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_AU);
  AU_exprt::check(expr);
  return static_cast<const AU_exprt &>(expr);
}

static inline AU_exprt &to_AU_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_AU);
  AU_exprt::check(expr);
  return static_cast<AU_exprt &>(expr);
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

class ER_exprt : public binary_predicate_exprt
{
public:
  explicit ER_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_ER, std::move(op1))
  {
  }
};

static inline const ER_exprt &to_ER_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_ER);
  R_exprt::check(expr);
  return static_cast<const ER_exprt &>(expr);
}

static inline ER_exprt &to_ER_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_ER);
  R_exprt::check(expr);
  return static_cast<ER_exprt &>(expr);
}

class AR_exprt : public binary_predicate_exprt
{
public:
  explicit AR_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_AR, std::move(op1))
  {
  }
};

static inline const AR_exprt &to_AR_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_AR);
  R_exprt::check(expr);
  return static_cast<const AR_exprt &>(expr);
}

static inline AR_exprt &to_AR_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_AR);
  R_exprt::check(expr);
  return static_cast<AR_exprt &>(expr);
}

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

class AX_exprt : public unary_predicate_exprt
{
public:
  explicit AX_exprt(exprt op) : unary_predicate_exprt(ID_AX, std::move(op))
  {
  }
};

static inline const AX_exprt &to_AX_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_AX);
  AX_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const AX_exprt &>(expr);
}

static inline AX_exprt &to_AX_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_AX);
  AX_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<AX_exprt &>(expr);
}

class EX_exprt : public unary_predicate_exprt
{
public:
  explicit EX_exprt(exprt op) : unary_predicate_exprt(ID_EX, std::move(op))
  {
  }
};

static inline const EX_exprt &to_EX_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_EX);
  EX_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const EX_exprt &>(expr);
}

static inline EX_exprt &to_EX_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_EX);
  EX_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<EX_exprt &>(expr);
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
