/*******************************************************************\

Module: System Verilog Asssertion Expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_SVA_EXPR_H
#define CPROVER_VERILOG_SVA_EXPR_H

#include <util/std_expr.h>

class sva_nexttime_exprt : public unary_predicate_exprt
{
public:
  explicit sva_nexttime_exprt(exprt op)
    : unary_predicate_exprt(ID_sva_nexttime, std::move(op))
  {
  }
};

static inline const sva_nexttime_exprt &to_sva_nexttime_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_nexttime);
  sva_nexttime_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_nexttime_exprt &>(expr);
}

static inline sva_nexttime_exprt &to_sva_nexttime_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_nexttime);
  sva_nexttime_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_nexttime_exprt &>(expr);
}

class sva_s_nexttime_exprt : public unary_predicate_exprt
{
public:
  explicit sva_s_nexttime_exprt(exprt op)
    : unary_predicate_exprt(ID_sva_s_nexttime, std::move(op))
  {
  }
};

static inline const sva_s_nexttime_exprt &
to_sva_s_nexttime_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_s_nexttime);
  sva_s_nexttime_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_s_nexttime_exprt &>(expr);
}

static inline sva_s_nexttime_exprt &to_sva_s_nexttime_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_s_nexttime);
  sva_s_nexttime_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_s_nexttime_exprt &>(expr);
}

class sva_eventually_exprt : public unary_predicate_exprt
{
public:
  explicit sva_eventually_exprt(exprt op)
    : unary_predicate_exprt(ID_sva_eventually, std::move(op))
  {
  }
};

static inline const sva_eventually_exprt &
to_sva_eventually_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_eventually);
  sva_eventually_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_eventually_exprt &>(expr);
}

static inline sva_eventually_exprt &to_sva_eventually_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_eventually);
  sva_eventually_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_eventually_exprt &>(expr);
}

class sva_s_eventually_exprt : public unary_predicate_exprt
{
public:
  explicit sva_s_eventually_exprt(exprt op)
    : unary_predicate_exprt(ID_sva_s_eventually, std::move(op))
  {
  }
};

static inline const sva_s_eventually_exprt &
to_sva_s_eventually_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_s_eventually);
  sva_s_eventually_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_s_eventually_exprt &>(expr);
}

static inline sva_s_eventually_exprt &to_sva_s_eventually_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_s_eventually);
  sva_s_eventually_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_s_eventually_exprt &>(expr);
}

class sva_always_exprt : public unary_predicate_exprt
{
public:
  explicit sva_always_exprt(exprt op)
    : unary_predicate_exprt(ID_sva_always, std::move(op))
  {
  }
};

static inline const sva_always_exprt &to_sva_always_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_always);
  sva_always_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_always_exprt &>(expr);
}

static inline sva_always_exprt &to_sva_always_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_always);
  sva_always_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_always_exprt &>(expr);
}

class sva_until_exprt : public binary_predicate_exprt
{
public:
  explicit sva_until_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_sva_until, std::move(op1))
  {
  }
};

static inline const sva_until_exprt &to_sva_until_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_until);
  sva_until_exprt::check(expr);
  return static_cast<const sva_until_exprt &>(expr);
}

static inline sva_until_exprt &to_sva_until_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_until);
  sva_until_exprt::check(expr);
  return static_cast<sva_until_exprt &>(expr);
}

class sva_s_until_exprt : public binary_predicate_exprt
{
public:
  explicit sva_s_until_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_sva_s_until, std::move(op1))
  {
  }
};

static inline const sva_s_until_exprt &to_sva_s_until_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_s_until);
  sva_s_until_exprt::check(expr);
  return static_cast<const sva_s_until_exprt &>(expr);
}

static inline sva_s_until_exprt &to_sva_s_until_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_s_until);
  sva_s_until_exprt::check(expr);
  return static_cast<sva_s_until_exprt &>(expr);
}

class sva_until_with_exprt : public binary_predicate_exprt
{
public:
  explicit sva_until_with_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_sva_until_with, std::move(op1))
  {
  }
};

static inline const sva_until_with_exprt &
to_sva_until_with_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_until_with);
  sva_until_with_exprt::check(expr);
  return static_cast<const sva_until_with_exprt &>(expr);
}

static inline sva_until_with_exprt &to_sva_until_with_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_until_with);
  sva_until_with_exprt::check(expr);
  return static_cast<sva_until_with_exprt &>(expr);
}

class sva_s_until_with_exprt : public binary_predicate_exprt
{
public:
  explicit sva_s_until_with_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(
        std::move(op0),
        ID_sva_s_until_with,
        std::move(op1))
  {
  }
};

static inline const sva_s_until_with_exprt &
to_sva_s_until_with_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_s_until_with);
  sva_s_until_with_exprt::check(expr);
  return static_cast<const sva_s_until_with_exprt &>(expr);
}

static inline sva_s_until_with_exprt &to_sva_s_until_with_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_s_until_with);
  sva_s_until_with_exprt::check(expr);
  return static_cast<sva_s_until_with_exprt &>(expr);
}

class sva_overlapped_implication_exprt : public binary_predicate_exprt
{
public:
  explicit sva_overlapped_implication_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(
        std::move(op0),
        ID_sva_overlapped_implication,
        std::move(op1))
  {
  }
};

static inline const sva_overlapped_implication_exprt &
to_sva_overlapped_implication_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_overlapped_implication);
  sva_overlapped_implication_exprt::check(expr);
  return static_cast<const sva_overlapped_implication_exprt &>(expr);
}

static inline sva_overlapped_implication_exprt &
to_sva_overlapped_implication_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_overlapped_implication);
  sva_overlapped_implication_exprt::check(expr);
  return static_cast<sva_overlapped_implication_exprt &>(expr);
}

class sva_non_overlapped_implication_exprt : public binary_predicate_exprt
{
public:
  explicit sva_non_overlapped_implication_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(
        std::move(op0),
        ID_sva_non_overlapped_implication,
        std::move(op1))
  {
  }
};

static inline const sva_non_overlapped_implication_exprt &
to_sva_non_overlapped_implication_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_non_overlapped_implication);
  sva_non_overlapped_implication_exprt::check(expr);
  return static_cast<const sva_non_overlapped_implication_exprt &>(expr);
}

static inline sva_non_overlapped_implication_exprt &
to_sva_non_overlapped_implication_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_non_overlapped_implication);
  sva_non_overlapped_implication_exprt::check(expr);
  return static_cast<sva_non_overlapped_implication_exprt &>(expr);
}

#endif
