/*******************************************************************\

Module: CTL Temporal Operators

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGIC_CTL_H
#define CPROVER_TEMPORAL_LOGIC_CTL_H

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
  ER_exprt::check(expr);
  return static_cast<const ER_exprt &>(expr);
}

static inline ER_exprt &to_ER_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_ER);
  ER_exprt::check(expr);
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
  AR_exprt::check(expr);
  return static_cast<const AR_exprt &>(expr);
}

static inline AR_exprt &to_AR_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_AR);
  AR_exprt::check(expr);
  return static_cast<AR_exprt &>(expr);
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

#endif
