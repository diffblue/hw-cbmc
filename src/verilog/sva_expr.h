/*******************************************************************\

Module: System Verilog Asssertion Expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_SVA_EXPR_H
#define CPROVER_VERILOG_SVA_EXPR_H

#include <util/std_expr.h>

/// accept_on, reject_on, sync_accept_on, sync_reject_on, disable_iff
class sva_abort_exprt : public binary_predicate_exprt
{
public:
  sva_abort_exprt(irep_idt id, exprt condition, exprt property)
    : binary_predicate_exprt(std::move(condition), id, std::move(property))
  {
  }

  const exprt &condition() const
  {
    return op0();
  }

  exprt &condition()
  {
    return op0();
  }

  const exprt &property() const
  {
    return op1();
  }

  exprt &property()
  {
    return op1();
  }

protected:
  using binary_predicate_exprt::op0;
  using binary_predicate_exprt::op1;
};

static inline const sva_abort_exprt &to_sva_abort_expr(const exprt &expr)
{
  sva_abort_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_abort_exprt &>(expr);
}

static inline sva_abort_exprt &to_sva_abort_expr(exprt &expr)
{
  sva_abort_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_abort_exprt &>(expr);
}

class sva_disable_iff_exprt : public sva_abort_exprt
{
public:
  sva_disable_iff_exprt(exprt condition, exprt property)
    : sva_abort_exprt(
        ID_sva_disable_iff,
        std::move(condition),
        std::move(property))
  {
  }
};

static inline const sva_disable_iff_exprt &
to_sva_disable_iff_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_disable_iff);
  sva_disable_iff_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_disable_iff_exprt &>(expr);
}

static inline sva_disable_iff_exprt &to_sva_disable_iff_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_disable_iff);
  sva_disable_iff_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_disable_iff_exprt &>(expr);
}

/// nonindexed variant
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

/// nonindexed variant
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

/// indexed variant of sva_nexttime_exprt
class sva_indexed_nexttime_exprt : public binary_predicate_exprt
{
public:
  sva_indexed_nexttime_exprt(exprt index, exprt op)
    : binary_predicate_exprt(
        std::move(index),
        ID_sva_indexed_nexttime,
        std::move(op))
  {
  }

  const exprt &index() const
  {
    return op0();
  }

  exprt &index()
  {
    return op0();
  }

  const exprt &op() const
  {
    return op1();
  }

  exprt &op()
  {
    return op1();
  }

protected:
  using binary_predicate_exprt::op0;
  using binary_predicate_exprt::op1;
};

static inline const sva_indexed_nexttime_exprt &
to_sva_indexed_nexttime_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_indexed_nexttime);
  sva_indexed_nexttime_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_indexed_nexttime_exprt &>(expr);
}

static inline sva_indexed_nexttime_exprt &
to_sva_indexed_nexttime_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_indexed_nexttime);
  sva_indexed_nexttime_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_indexed_nexttime_exprt &>(expr);
}

/// indexed variant of sva_s_nexttime_exprt
class sva_indexed_s_nexttime_exprt : public binary_predicate_exprt
{
public:
  sva_indexed_s_nexttime_exprt(exprt index, exprt op)
    : binary_predicate_exprt(
        std::move(index),
        ID_sva_indexed_s_nexttime,
        std::move(op))
  {
  }

  const exprt &index() const
  {
    return op0();
  }

  exprt &index()
  {
    return op0();
  }

  const exprt &op() const
  {
    return op1();
  }

  exprt &op()
  {
    return op1();
  }

protected:
  using binary_predicate_exprt::op0;
  using binary_predicate_exprt::op1;
};

static inline const sva_indexed_s_nexttime_exprt &
to_sva_indexed_s_nexttime_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_indexed_s_nexttime);
  sva_indexed_s_nexttime_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_indexed_s_nexttime_exprt &>(expr);
}

static inline sva_indexed_s_nexttime_exprt &
to_sva_indexed_s_nexttime_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_indexed_s_nexttime);
  sva_indexed_s_nexttime_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_indexed_s_nexttime_exprt &>(expr);
}

class sva_ranged_predicate_exprt : public ternary_exprt
{
public:
  sva_ranged_predicate_exprt(
    irep_idt __id,
    exprt __lower,
    exprt __upper,
    exprt __op)
    : ternary_exprt(
        __id,
        std::move(__lower),
        std::move(__upper),
        std::move(__op),
        bool_typet())
  {
  }

  const exprt &lower() const
  {
    return op0();
  }

  exprt &lower()
  {
    return op0();
  }

  const exprt &upper() const
  {
    return op1();
  }

  exprt &upper()
  {
    return op1();
  }

  const exprt &op() const
  {
    return op2();
  }

  exprt &op()
  {
    return op2();
  }

protected:
  using ternary_exprt::op0;
  using ternary_exprt::op1;
  using ternary_exprt::op2;
};

class sva_eventually_exprt : public sva_ranged_predicate_exprt
{
public:
  sva_eventually_exprt(exprt __lower, exprt __upper, exprt __op)
    : sva_ranged_predicate_exprt(
        ID_sva_eventually,
        std::move(__lower),
        std::move(__upper),
        std::move(__op))
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

class sva_ranged_s_eventually_exprt : public sva_ranged_predicate_exprt
{
public:
  explicit sva_ranged_s_eventually_exprt(exprt lower, exprt upper, exprt op)
    : sva_ranged_predicate_exprt(
        ID_sva_ranged_s_eventually,
        std::move(lower),
        std::move(upper),
        std::move(op))
  {
  }
};

static inline const sva_ranged_s_eventually_exprt &
to_sva_ranged_s_eventually_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_ranged_s_eventually);
  sva_ranged_s_eventually_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_ranged_s_eventually_exprt &>(expr);
}

static inline sva_ranged_s_eventually_exprt &
to_sva_ranged_s_eventually_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_ranged_s_eventually);
  sva_ranged_s_eventually_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_ranged_s_eventually_exprt &>(expr);
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

class sva_ranged_always_exprt : public sva_ranged_predicate_exprt
{
public:
  sva_ranged_always_exprt(exprt lower, exprt upper, exprt op)
    : sva_ranged_predicate_exprt(
        ID_sva_ranged_always,
        std::move(lower),
        std::move(upper),
        std::move(op))
  {
  }
};

static inline const sva_ranged_always_exprt &
to_sva_ranged_always_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_ranged_always);
  sva_ranged_always_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_ranged_always_exprt &>(expr);
}

static inline sva_ranged_always_exprt &to_sva_ranged_always_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_ranged_always);
  sva_ranged_always_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_ranged_always_exprt &>(expr);
}

class sva_s_always_exprt : public sva_ranged_predicate_exprt
{
public:
  sva_s_always_exprt(exprt lower, exprt upper, exprt op)
    : sva_ranged_predicate_exprt(
        ID_sva_s_always,
        std::move(lower),
        std::move(upper),
        std::move(op))
  {
  }
};

static inline const sva_s_always_exprt &to_sva_s_always_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_s_always);
  sva_s_always_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_s_always_exprt &>(expr);
}

static inline sva_s_always_exprt &to_sva_s_always_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_s_always);
  sva_s_always_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_s_always_exprt &>(expr);
}

class sva_cover_exprt : public unary_predicate_exprt
{
public:
  explicit sva_cover_exprt(exprt op)
    : unary_predicate_exprt(ID_sva_cover, std::move(op))
  {
  }
};

static inline const sva_cover_exprt &to_sva_cover_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_cover);
  sva_cover_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_cover_exprt &>(expr);
}

static inline sva_cover_exprt &to_sva_cover_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_cover);
  sva_cover_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_cover_exprt &>(expr);
}

class sva_assume_exprt : public unary_predicate_exprt
{
public:
  explicit sva_assume_exprt(exprt op)
    : unary_predicate_exprt(ID_sva_assume, std::move(op))
  {
  }
};

static inline const sva_assume_exprt &to_sva_assume_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_assume);
  sva_assume_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_assume_exprt &>(expr);
}

static inline sva_assume_exprt &to_sva_assume_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_assume);
  sva_assume_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_assume_exprt &>(expr);
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

/// SVA until_with operator -- like LTL (weak) R, but lhs/rhs swapped
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

/// SVA s_until_with operator -- like LTL strong R, but lhs/rhs swapped
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

class sva_not_exprt : public unary_predicate_exprt
{
public:
  explicit sva_not_exprt(exprt op)
    : unary_predicate_exprt(ID_sva_not, std::move(op))
  {
  }
};

static inline const sva_not_exprt &to_sva_not_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_not);
  sva_not_exprt::check(expr);
  return static_cast<const sva_not_exprt &>(expr);
}

static inline sva_not_exprt &to_sva_not_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_not);
  sva_not_exprt::check(expr);
  return static_cast<sva_not_exprt &>(expr);
}

class sva_and_exprt : public binary_predicate_exprt
{
public:
  explicit sva_and_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_sva_and, std::move(op1))
  {
  }
};

static inline const sva_and_exprt &to_sva_and_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_and);
  sva_and_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_and_exprt &>(expr);
}

static inline sva_and_exprt &to_sva_and_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_and);
  sva_and_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_and_exprt &>(expr);
}

class sva_sequence_concatenation_exprt : public binary_predicate_exprt
{
public:
  explicit sva_sequence_concatenation_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(
        std::move(op0),
        ID_sva_sequence_concatenation,
        std::move(op1))
  {
  }
};

static inline const sva_sequence_concatenation_exprt &
to_sva_sequence_concatenation_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_concatenation);
  sva_sequence_concatenation_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_sequence_concatenation_exprt &>(expr);
}

static inline sva_sequence_concatenation_exprt &
to_sva_sequence_concatenation_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_concatenation);
  sva_sequence_concatenation_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_sequence_concatenation_exprt &>(expr);
}

class sva_iff_exprt : public binary_predicate_exprt
{
public:
  explicit sva_iff_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_sva_iff, std::move(op1))
  {
  }
};

static inline const sva_iff_exprt &to_sva_iff_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_iff);
  sva_iff_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_iff_exprt &>(expr);
}

static inline sva_iff_exprt &to_sva_iff_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_iff);
  sva_iff_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_iff_exprt &>(expr);
}

class sva_implies_exprt : public binary_predicate_exprt
{
public:
  explicit sva_implies_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_sva_implies, std::move(op1))
  {
  }
};

static inline const sva_implies_exprt &to_sva_implies_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_implies);
  sva_implies_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_implies_exprt &>(expr);
}

static inline sva_implies_exprt &to_sva_implies_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_implies);
  sva_implies_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_implies_exprt &>(expr);
}

class sva_or_exprt : public binary_predicate_exprt
{
public:
  explicit sva_or_exprt(exprt op0, exprt op1)
    : binary_predicate_exprt(std::move(op0), ID_sva_or, std::move(op1))
  {
  }
};

static inline const sva_or_exprt &to_sva_or_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_or);
  sva_or_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_or_exprt &>(expr);
}

static inline sva_or_exprt &to_sva_or_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_or);
  sva_or_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_or_exprt &>(expr);
}

class sva_followed_by_exprt : public binary_predicate_exprt
{
public:
  const exprt &sequence() const
  {
    return op0();
  }

  exprt &sequence()
  {
    return op0();
  }

  const exprt &property() const
  {
    return op1();
  }

  exprt &property()
  {
    return op1();
  }
};

static inline const sva_followed_by_exprt &
to_sva_followed_by_expr(const exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_sva_overlapped_followed_by ||
    expr.id() == ID_sva_nonoverlapped_followed_by);
  sva_followed_by_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_followed_by_exprt &>(expr);
}

static inline sva_followed_by_exprt &to_sva_followed_by_expr(exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_sva_overlapped_followed_by ||
    expr.id() == ID_sva_nonoverlapped_followed_by);
  sva_followed_by_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_followed_by_exprt &>(expr);
}

class sva_cycle_delay_exprt : public ternary_exprt
{
public:
  sva_cycle_delay_exprt(exprt from, exprt to, exprt op)
    : ternary_exprt(
        ID_sva_cycle_delay,
        std::move(from),
        std::move(to),
        std::move(op),
        bool_typet())
  {
  }

  sva_cycle_delay_exprt(exprt cycles, exprt op)
    : ternary_exprt(
        ID_sva_cycle_delay,
        std::move(cycles),
        nil_exprt{},
        std::move(op),
        bool_typet())
  {
  }

  const exprt &from() const
  {
    return op0();
  }

  exprt &from()
  {
    return op0();
  }

  // may be nil (just the singleton 'from') or
  // infinity (half-open interval starting at 'from')
  const exprt &to() const
  {
    return op1();
  }

  exprt &to()
  {
    return op1();
  }

  bool is_unbounded() const
  {
    return to().id() == ID_infinity;
  }

  const exprt &op() const
  {
    return op2();
  }

  exprt &op()
  {
    return op2();
  }

protected:
  using ternary_exprt::op0;
  using ternary_exprt::op1;
  using ternary_exprt::op2;
};

static inline const sva_cycle_delay_exprt &
to_sva_cycle_delay_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_cycle_delay);
  sva_cycle_delay_exprt::check(expr);
  return static_cast<const sva_cycle_delay_exprt &>(expr);
}

static inline sva_cycle_delay_exprt &to_sva_cycle_delay_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_cycle_delay);
  sva_cycle_delay_exprt::check(expr);
  return static_cast<sva_cycle_delay_exprt &>(expr);
}

class sva_cycle_delay_plus_exprt : public unary_exprt
{
public:
  explicit sva_cycle_delay_plus_exprt(exprt op)
    : unary_exprt(ID_sva_cycle_delay_plus, std::move(op), bool_typet())
  {
  }
};

static inline const sva_cycle_delay_plus_exprt &
to_sva_cycle_delay_plus_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_cycle_delay_plus);
  sva_cycle_delay_plus_exprt::check(expr);
  return static_cast<const sva_cycle_delay_plus_exprt &>(expr);
}

static inline sva_cycle_delay_plus_exprt &
to_sva_cycle_delay_plus_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_cycle_delay_plus);
  sva_cycle_delay_plus_exprt::check(expr);
  return static_cast<sva_cycle_delay_plus_exprt &>(expr);
}

class sva_cycle_delay_star_exprt : public unary_exprt
{
public:
  explicit sva_cycle_delay_star_exprt(exprt op)
    : unary_exprt(ID_sva_cycle_delay_star, std::move(op), bool_typet())
  {
  }
};

static inline const sva_cycle_delay_star_exprt &
to_sva_cycle_delay_star_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_cycle_delay_star);
  sva_cycle_delay_star_exprt::check(expr);
  return static_cast<const sva_cycle_delay_star_exprt &>(expr);
}

static inline sva_cycle_delay_star_exprt &
to_sva_cycle_delay_star_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_cycle_delay_star);
  sva_cycle_delay_star_exprt::check(expr);
  return static_cast<sva_cycle_delay_star_exprt &>(expr);
}

class sva_if_exprt : public ternary_exprt
{
public:
  explicit sva_if_exprt(exprt __cond, exprt __true_case, exprt __false_case)
    : ternary_exprt(
        ID_sva_if,
        std::move(__cond),
        std::move(__true_case),
        std::move(__false_case),
        bool_typet())
  {
  }

  const exprt &cond() const
  {
    return op0();
  }

  exprt &cond()
  {
    return op0();
  }

  const exprt &true_case() const
  {
    return op1();
  }

  exprt &true_case()
  {
    return op1();
  }

  // may be nil (in which case it defaults to 'true')
  const exprt &false_case() const
  {
    return op2();
  }

  exprt &false_case()
  {
    return op2();
  }

protected:
  using ternary_exprt::op0;
  using ternary_exprt::op1;
  using ternary_exprt::op2;
};

static inline const sva_if_exprt &to_sva_if_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_if);
  sva_if_exprt::check(expr);
  return static_cast<const sva_if_exprt &>(expr);
}

static inline sva_if_exprt &to_sva_if_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_if);
  sva_if_exprt::check(expr);
  return static_cast<sva_if_exprt &>(expr);
}

class sva_strong_exprt : public unary_exprt
{
public:
  sva_strong_exprt(exprt __op, typet __type)
    : unary_exprt(ID_sva_strong, std::move(__op), std::move(__type))
  {
  }
};

inline const sva_strong_exprt &to_sva_strong_expr(const exprt &expr)
{
  sva_strong_exprt::check(expr);
  return static_cast<const sva_strong_exprt &>(expr);
}

inline sva_strong_exprt &to_sva_strong_expr(exprt &expr)
{
  sva_strong_exprt::check(expr);
  return static_cast<sva_strong_exprt &>(expr);
}

class sva_weak_exprt : public unary_exprt
{
public:
  sva_weak_exprt(exprt __op, typet __type)
    : unary_exprt(ID_sva_weak, std::move(__op), std::move(__type))
  {
  }
};

inline const sva_weak_exprt &to_sva_weak_expr(const exprt &expr)
{
  sva_weak_exprt::check(expr);
  return static_cast<const sva_weak_exprt &>(expr);
}

inline sva_weak_exprt &to_sva_weak_expr(exprt &expr)
{
  sva_weak_exprt::check(expr);
  return static_cast<sva_weak_exprt &>(expr);
}

class sva_case_exprt : public binary_predicate_exprt
{
public:
  explicit sva_case_exprt(exprt __case_op, exprt __cases)
    : binary_predicate_exprt(
        std::move(__case_op),
        ID_sva_case,
        std::move(__cases))
  {
  }

  const exprt &case_op() const
  {
    return op0();
  }

  exprt &case_op()
  {
    return op0();
  }

  class case_itemt : public binary_exprt
  {
  public:
    const exprt::operandst &patterns() const
    {
      return op0().operands();
    }

    exprt::operandst &patterns()
    {
      return op0().operands();
    }

    const exprt &result() const
    {
      return op1();
    }

    exprt &result()
    {
      return op1();
    }

  protected:
    using binary_exprt::op0;
    using binary_exprt::op1;
  };

  using case_itemst = std::vector<case_itemt>;

  const case_itemst &case_items() const
  {
    return (const case_itemst &)(op1().operands());
  }

  case_itemst &case_items()
  {
    return (case_itemst &)(op1().operands());
  }

  exprt lowering() const;

protected:
  using binary_predicate_exprt::op0;
  using binary_predicate_exprt::op1;
};

inline const sva_case_exprt &to_sva_case_expr(const exprt &expr)
{
  sva_case_exprt::check(expr);
  return static_cast<const sva_case_exprt &>(expr);
}

inline sva_case_exprt &to_sva_case_expr(exprt &expr)
{
  sva_case_exprt::check(expr);
  return static_cast<sva_case_exprt &>(expr);
}

class sva_sequence_consecutive_repetition_exprt : public binary_predicate_exprt
{
public:
  exprt lower() const;

protected:
  using binary_predicate_exprt::op0;
  using binary_predicate_exprt::op1;
};

inline const sva_sequence_consecutive_repetition_exprt &
to_sva_sequence_consecutive_repetition_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_consecutive_repetition);
  sva_sequence_consecutive_repetition_exprt::check(expr);
  return static_cast<const sva_sequence_consecutive_repetition_exprt &>(expr);
}

inline sva_sequence_consecutive_repetition_exprt &
to_sva_sequence_consecutive_repetition_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_consecutive_repetition);
  sva_sequence_consecutive_repetition_exprt::check(expr);
  return static_cast<sva_sequence_consecutive_repetition_exprt &>(expr);
}

class sva_sequence_intersect_exprt : public binary_exprt
{
public:
  sva_sequence_intersect_exprt(exprt op0, exprt op1)
    : binary_exprt(std::move(op0), ID_sva_sequence_intersect, std::move(op1))
  {
  }
};

static inline const sva_sequence_intersect_exprt &
to_sva_sequence_intersect_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_intersect);
  sva_sequence_intersect_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_sequence_intersect_exprt &>(expr);
}

static inline sva_sequence_intersect_exprt &
to_sva_sequence_intersect_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_intersect);
  sva_sequence_intersect_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_sequence_intersect_exprt &>(expr);
}

#endif
