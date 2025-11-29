/*******************************************************************\

Module: System Verilog Asssertion Expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_SVA_EXPR_H
#define CPROVER_VERILOG_SVA_EXPR_H

#include <util/std_expr.h>

#include "verilog_expr.h"
#include "verilog_types.h"

/// 1800-2017 16.6 Boolean expressions
/// Conversion of a Boolean expression into a sequence or property
class sva_boolean_exprt : public unary_exprt
{
public:
  sva_boolean_exprt(exprt condition, typet __type)
    : unary_exprt(ID_sva_boolean, std::move(condition), std::move(__type))
  {
  }
};

static inline const sva_boolean_exprt &to_sva_boolean_expr(const exprt &expr)
{
  sva_boolean_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_boolean_exprt &>(expr);
}

static inline sva_boolean_exprt &to_sva_boolean_expr(exprt &expr)
{
  sva_boolean_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_boolean_exprt &>(expr);
}

/// disable_iff for cover sequence
class sva_sequence_disable_iff_exprt : public binary_exprt
{
public:
  sva_sequence_disable_iff_exprt(exprt condition, exprt sequence)
    : binary_exprt(
        std::move(condition),
        ID_sva_sequence_disable_iff,
        std::move(sequence),
        verilog_sva_sequence_typet{})
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

  const exprt &sequence() const
  {
    return op1();
  }

  exprt &sequence()
  {
    return op1();
  }

protected:
  using binary_exprt::op0;
  using binary_exprt::op1;
};

static inline const sva_sequence_disable_iff_exprt &
to_sva_sequence_disable_iff_expr(const exprt &expr)
{
  sva_sequence_disable_iff_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_sequence_disable_iff_exprt &>(expr);
}

static inline sva_sequence_disable_iff_exprt &
to_sva_sequence_disable_iff_expr(exprt &expr)
{
  sva_sequence_disable_iff_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_sequence_disable_iff_exprt &>(expr);
}

/// accept_on, reject_on, sync_accept_on, sync_reject_on, disable_iff
class sva_abort_exprt : public binary_exprt
{
public:
  sva_abort_exprt(irep_idt id, exprt condition, exprt property)
    : binary_exprt(
        std::move(condition),
        id,
        std::move(property),
        verilog_sva_property_typet{})
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
  using binary_exprt::op0;
  using binary_exprt::op1;
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
class sva_nexttime_exprt : public unary_exprt
{
public:
  explicit sva_nexttime_exprt(exprt op)
    : unary_exprt(ID_sva_nexttime, std::move(op), verilog_sva_property_typet{})
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
class sva_s_nexttime_exprt : public unary_exprt
{
public:
  explicit sva_s_nexttime_exprt(exprt op)
    : unary_exprt(
        ID_sva_s_nexttime,
        std::move(op),
        verilog_sva_property_typet{})
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
class sva_indexed_nexttime_exprt : public binary_exprt
{
public:
  sva_indexed_nexttime_exprt(constant_exprt index, exprt op)
    : binary_exprt(
        std::move(index),
        ID_sva_indexed_nexttime,
        std::move(op),
        verilog_sva_property_typet{})
  {
  }

  const constant_exprt &index() const
  {
    return static_cast<const constant_exprt &>(op0());
  }

  constant_exprt &index()
  {
    return static_cast<constant_exprt &>(op0());
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
  using binary_exprt::op0;
  using binary_exprt::op1;
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
class sva_indexed_s_nexttime_exprt : public binary_exprt
{
public:
  sva_indexed_s_nexttime_exprt(constant_exprt index, exprt op)
    : binary_exprt(
        std::move(index),
        ID_sva_indexed_s_nexttime,
        std::move(op),
        verilog_sva_property_typet{})
  {
  }

  const constant_exprt &index() const
  {
    return static_cast<const constant_exprt &>(op0());
  }

  constant_exprt &index()
  {
    return static_cast<constant_exprt &>(op0());
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
  using binary_exprt::op0;
  using binary_exprt::op1;
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

/// For ranged SVA operators. The lower bound must be a constant
/// post elaboration. The upper end need not be bounded,
/// i.e., given as $
class sva_ranged_predicate_exprt : public ternary_exprt
{
public:
  sva_ranged_predicate_exprt(
    irep_idt __id,
    constant_exprt __from,
    exprt __to,
    exprt __op)
    : ternary_exprt(
        __id,
        std::move(__from),
        std::move(__to),
        std::move(__op),
        verilog_sva_property_typet{})
  {
  }

  sva_ranged_predicate_exprt(
    irep_idt __id,
    constant_exprt __from,
    exprt __to,
    exprt __op,
    typet __type)
    : ternary_exprt(
        __id,
        std::move(__from),
        std::move(__to),
        std::move(__op),
        std::move(__type))
  {
  }

  const constant_exprt &from() const
  {
    return static_cast<const constant_exprt &>(op0());
  }

  constant_exprt &from()
  {
    return static_cast<constant_exprt &>(op0());
  }

  bool is_range() const
  {
    return op1().is_not_nil();
  }

  bool is_unbounded() const
  {
    return op1().id() == ID_infinity;
  }

  const exprt &to() const
  {
    return op1();
  }

  exprt &to()
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

static inline const sva_ranged_predicate_exprt &
to_sva_ranged_predicate_exprt(const exprt &expr)
{
  sva_ranged_predicate_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_ranged_predicate_exprt &>(expr);
}

static inline sva_ranged_predicate_exprt &
to_sva_ranged_predicate_exprt(exprt &expr)
{
  sva_ranged_predicate_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_ranged_predicate_exprt &>(expr);
}

/// A specialisation of sva_ranged_predicate_exprt where both bounds
/// are constants.
class sva_bounded_range_predicate_exprt : public sva_ranged_predicate_exprt
{
public:
  sva_bounded_range_predicate_exprt(
    irep_idt __id,
    constant_exprt __from,
    constant_exprt __to,
    exprt __op)
    : sva_ranged_predicate_exprt(
        __id,
        std::move(__from),
        std::move(__to),
        std::move(__op))
  {
  }

  sva_bounded_range_predicate_exprt(
    irep_idt __id,
    constant_exprt __from,
    constant_exprt __to,
    exprt __op,
    typet __type)
    : sva_ranged_predicate_exprt(
        __id,
        std::move(__from),
        std::move(__to),
        std::move(__op),
        std::move(__type))
  {
  }

  const constant_exprt &to() const
  {
    return static_cast<const constant_exprt &>(
      sva_ranged_predicate_exprt::to());
  }

  constant_exprt &to()
  {
    return static_cast<constant_exprt &>(sva_ranged_predicate_exprt::to());
  }
};

class sva_eventually_exprt : public sva_bounded_range_predicate_exprt
{
public:
  sva_eventually_exprt(constant_exprt __from, constant_exprt __to, exprt __op)
    : sva_bounded_range_predicate_exprt(
        ID_sva_eventually,
        std::move(__from),
        std::move(__to),
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

class sva_s_eventually_exprt : public unary_exprt
{
public:
  explicit sva_s_eventually_exprt(exprt op)
    : unary_exprt(
        ID_sva_s_eventually,
        std::move(op),
        verilog_sva_property_typet{})
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
  explicit sva_ranged_s_eventually_exprt(
    constant_exprt from,
    exprt to,
    exprt op)
    : sva_ranged_predicate_exprt(
        ID_sva_ranged_s_eventually,
        std::move(from),
        std::move(to),
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

class sva_always_exprt : public unary_exprt
{
public:
  explicit sva_always_exprt(exprt op)
    : unary_exprt(ID_sva_always, std::move(op), verilog_sva_property_typet{})
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
  sva_ranged_always_exprt(constant_exprt from, exprt to, exprt op)
    : sva_ranged_predicate_exprt(
        ID_sva_ranged_always,
        std::move(from),
        std::move(to),
        std::move(op))
  {
  }

  sva_ranged_always_exprt(constant_exprt from, exprt to, exprt op, typet __type)
    : sva_ranged_predicate_exprt(
        ID_sva_ranged_always,
        std::move(from),
        std::move(to),
        std::move(op),
        std::move(__type))
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

class sva_s_always_exprt : public sva_bounded_range_predicate_exprt
{
public:
  sva_s_always_exprt(constant_exprt from, constant_exprt to, exprt op)
    : sva_bounded_range_predicate_exprt(
        ID_sva_s_always,
        std::move(from),
        std::move(to),
        std::move(op))
  {
  }

  sva_s_always_exprt(
    constant_exprt from,
    constant_exprt to,
    exprt op,
    typet __type)
    : sva_bounded_range_predicate_exprt(
        ID_sva_s_always,
        std::move(from),
        std::move(to),
        std::move(op),
        std::move(__type))
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

class sva_cover_exprt : public unary_exprt
{
public:
  explicit sva_cover_exprt(exprt op)
    : unary_exprt(ID_sva_cover, std::move(op), verilog_sva_property_typet{})
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

class sva_assume_exprt : public unary_exprt
{
public:
  explicit sva_assume_exprt(exprt op)
    : unary_exprt(ID_sva_assume, std::move(op), verilog_sva_property_typet{})
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

class sva_until_exprt : public binary_exprt
{
public:
  explicit sva_until_exprt(exprt op0, exprt op1)
    : binary_exprt(
        std::move(op0),
        ID_sva_until,
        std::move(op1),
        verilog_sva_property_typet{})
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

class sva_s_until_exprt : public binary_exprt
{
public:
  explicit sva_s_until_exprt(exprt op0, exprt op1)
    : binary_exprt(
        std::move(op0),
        ID_sva_s_until,
        std::move(op1),
        verilog_sva_property_typet{})
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
class sva_until_with_exprt : public binary_exprt
{
public:
  explicit sva_until_with_exprt(exprt op0, exprt op1)
    : binary_exprt(
        std::move(op0),
        ID_sva_until_with,
        std::move(op1),
        verilog_sva_property_typet{})
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
class sva_s_until_with_exprt : public binary_exprt
{
public:
  explicit sva_s_until_with_exprt(exprt op0, exprt op1)
    : binary_exprt(
        std::move(op0),
        ID_sva_s_until_with,
        std::move(op1),
        verilog_sva_property_typet{})
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

/// base class for |->, |=>, #-#, #=#
class sva_implication_base_exprt : public binary_exprt
{
public:
  sva_implication_base_exprt(
    exprt __antecedent,
    irep_idt __id,
    exprt __consequent)
    : binary_exprt(
        std::move(__antecedent),
        __id,
        std::move(__consequent),
        verilog_sva_property_typet{})
  {
  }

  sva_implication_base_exprt(
    exprt __antecedent,
    irep_idt __id,
    exprt __consequent,
    typet __type)
    : binary_exprt(
        std::move(__antecedent),
        __id,
        std::move(__consequent),
        std::move(__type))
  {
  }

  // a sequence
  const exprt &antecedent() const
  {
    return lhs();
  }

  exprt &antecedent()
  {
    return lhs();
  }

  const exprt &sequence() const
  {
    return op0();
  }

  exprt &sequence()
  {
    return op0();
  }

  // a property
  const exprt &consequent() const
  {
    return rhs();
  }

  exprt &consequent()
  {
    return rhs();
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

static inline const sva_implication_base_exprt &
to_sva_implication_base_expr(const exprt &expr)
{
  sva_implication_base_exprt::check(expr);
  return static_cast<const sva_implication_base_exprt &>(expr);
}

static inline sva_implication_base_exprt &
to_sva_implication_base_expr(exprt &expr)
{
  sva_implication_base_exprt::check(expr);
  return static_cast<sva_implication_base_exprt &>(expr);
}

/// |->
class sva_overlapped_implication_exprt : public sva_implication_base_exprt
{
public:
  sva_overlapped_implication_exprt(exprt __antecedent, exprt __consequent)
    : sva_implication_base_exprt(
        std::move(__antecedent),
        ID_sva_overlapped_implication,
        std::move(__consequent))
  {
  }

  sva_overlapped_implication_exprt(
    exprt __antecedent,
    exprt __consequent,
    typet __type)
    : sva_implication_base_exprt(
        std::move(__antecedent),
        ID_sva_overlapped_implication,
        std::move(__consequent),
        std::move(__type))
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

/// |=>
class sva_non_overlapped_implication_exprt : public sva_implication_base_exprt
{
public:
  sva_non_overlapped_implication_exprt(exprt __antecedent, exprt __consequent)
    : sva_implication_base_exprt(
        std::move(__antecedent),
        ID_sva_non_overlapped_implication,
        std::move(__consequent))
  {
  }

  sva_non_overlapped_implication_exprt(
    exprt __antecedent,
    exprt __consequent,
    typet __type)
    : sva_implication_base_exprt(
        std::move(__antecedent),
        ID_sva_non_overlapped_implication,
        std::move(__consequent),
        std::move(__type))
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

class sva_not_exprt : public unary_exprt
{
public:
  explicit sva_not_exprt(exprt op)
    : unary_exprt(ID_sva_not, std::move(op), verilog_sva_property_typet{})
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

class sva_and_exprt : public binary_exprt
{
public:
  // can be a sequence or property, depending on operands
  explicit sva_and_exprt(exprt op0, exprt op1, typet __type)
    : binary_exprt(
        std::move(op0),
        ID_sva_and,
        std::move(op1),
        std::move(__type))
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

class sva_iff_exprt : public binary_exprt
{
public:
  explicit sva_iff_exprt(exprt op0, exprt op1)
    : binary_exprt(
        std::move(op0),
        ID_sva_iff,
        std::move(op1),
        verilog_sva_property_typet{})
  {
  }

  // (lhs implies rhs) and (rhs implies lhs)
  exprt implications() const;
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

class sva_implies_exprt : public binary_exprt
{
public:
  explicit sva_implies_exprt(exprt op0, exprt op1)
    : binary_exprt(
        std::move(op0),
        ID_sva_implies,
        std::move(op1),
        verilog_sva_property_typet{})
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

class sva_or_exprt : public binary_exprt
{
public:
  // These can be sequences or properties, depending on the operands
  explicit sva_or_exprt(exprt op0, exprt op1, typet __type)
    : binary_exprt(std::move(op0), ID_sva_or, std::move(op1), std::move(__type))
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

// #-#, #=#
class sva_followed_by_exprt : public sva_implication_base_exprt
{
public:
  explicit sva_followed_by_exprt(
    exprt __antecedent,
    irep_idt __id,
    exprt __consequent)
    : sva_implication_base_exprt(
        std::move(__antecedent),
        __id,
        std::move(__consequent))
  {
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

/// lhs ##n rhs
/// lhs ##[from:to] rhs
/// lhs ##[from:$] rhs
/// The lhs is optional, indicated by 'nil'
class sva_cycle_delay_exprt : public exprt
{
public:
  /// The upper bound may be $
  sva_cycle_delay_exprt(exprt lhs, constant_exprt from, exprt to, exprt rhs)
    : exprt{
        ID_sva_cycle_delay,
        verilog_sva_sequence_typet{},
        {std::move(lhs), std::move(from), std::move(to), std::move(rhs)}}
  {
  }

  sva_cycle_delay_exprt(constant_exprt cycles, exprt rhs)
    : exprt{
        ID_sva_cycle_delay,
        verilog_sva_sequence_typet{},
        {nil_exprt{}, std::move(cycles), nil_exprt{}, std::move(rhs)}}
  {
  }

  const exprt &lhs() const
  {
    return operands()[0];
  }

  exprt &lhs()
  {
    return operands()[0];
  }

  const constant_exprt &from() const
  {
    return static_cast<const constant_exprt &>(operands()[1]);
  }

  constant_exprt &from()
  {
    return static_cast<constant_exprt &>(operands()[1]);
  }

  // May be just the singleton 'from' or
  // a half-open interval starting at 'from'.
  // Use is_range() and is_unbounded() to distinguish.
  const constant_exprt &to() const
  {
    PRECONDITION(is_range() && !is_unbounded());
    return static_cast<const constant_exprt &>(operands()[2]);
  }

  constant_exprt &to()
  {
    PRECONDITION(is_range() && !is_unbounded());
    return static_cast<constant_exprt &>(operands()[2]);
  }

  bool is_range() const
  {
    return operands()[2].is_not_nil();
  }

  bool is_unbounded() const
  {
    return operands()[2].id() == ID_infinity;
  }

  const exprt &rhs() const
  {
    return operands()[3];
  }

  exprt &rhs()
  {
    return operands()[3];
  }

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm,
      expr.operands().size() == 4,
      "sva_cycle_delay expression must have four operands");
  }
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

class sva_cycle_delay_plus_exprt : public binary_exprt
{
public:
  /// The operands are sequences, the LHS is optional, indicated by nil.
  explicit sva_cycle_delay_plus_exprt(exprt __lhs, exprt __rhs)
    : binary_exprt(
        std::move(__lhs),
        ID_sva_cycle_delay_plus,
        std::move(__rhs),
        verilog_sva_sequence_typet{})
  {
  }

  bool has_lhs() const
  {
    return lhs().is_not_nil();
  }

  // ##[1:$] op
  exprt lower() const;
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

class sva_cycle_delay_star_exprt : public binary_exprt
{
public:
  /// The operands are a sequences, the LHS is optional, indicated by nil.
  explicit sva_cycle_delay_star_exprt(exprt __lhs, exprt __rhs)
    : binary_exprt(
        std::move(__lhs),
        ID_sva_cycle_delay_star,
        std::move(__rhs),
        verilog_sva_sequence_typet{})
  {
  }

  bool has_lhs() const
  {
    return lhs().is_not_nil();
  }

  // ##[0:$] op
  exprt lower() const;
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
        verilog_sva_property_typet{})
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

/// Base class for sequence property expressions.
/// 1800-2017 16.12.2 Sequence property
class sva_sequence_property_expr_baset : public unary_exprt
{
public:
  sva_sequence_property_expr_baset(irep_idt __id, exprt __op)
    : unary_exprt(__id, std::move(__op), verilog_sva_property_typet{})
  {
  }

  const exprt &sequence() const
  {
    return op();
  }

  exprt &sequence()
  {
    return op();
  }

protected:
  using unary_exprt::op;
};

inline const sva_sequence_property_expr_baset &
to_sva_sequence_property_expr_base(const exprt &expr)
{
  sva_sequence_property_expr_baset::check(expr);
  return static_cast<const sva_sequence_property_expr_baset &>(expr);
}

inline sva_sequence_property_expr_baset &
to_sva_sequence_property_expr_base(exprt &expr)
{
  sva_sequence_property_expr_baset::check(expr);
  return static_cast<sva_sequence_property_expr_baset &>(expr);
}

class sva_strong_exprt : public sva_sequence_property_expr_baset
{
public:
  sva_strong_exprt(irep_idt __id, exprt __op)
    : sva_sequence_property_expr_baset(__id, std::move(__op))
  {
  }
};

inline const sva_strong_exprt &to_sva_strong_expr(const exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_sva_strong || expr.id() == ID_sva_implicit_strong);
  sva_strong_exprt::check(expr);
  return static_cast<const sva_strong_exprt &>(expr);
}

inline sva_strong_exprt &to_sva_strong_expr(exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_sva_strong || expr.id() == ID_sva_implicit_strong);
  sva_strong_exprt::check(expr);
  return static_cast<sva_strong_exprt &>(expr);
}

class sva_weak_exprt : public sva_sequence_property_expr_baset
{
public:
  sva_weak_exprt(irep_idt __id, exprt __op)
    : sva_sequence_property_expr_baset(__id, std::move(__op))
  {
  }
};

inline const sva_weak_exprt &to_sva_weak_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_weak || expr.id() == ID_sva_implicit_weak);
  sva_weak_exprt::check(expr);
  return static_cast<const sva_weak_exprt &>(expr);
}

inline sva_weak_exprt &to_sva_weak_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_weak || expr.id() == ID_sva_implicit_weak);
  sva_weak_exprt::check(expr);
  return static_cast<sva_weak_exprt &>(expr);
}

class sva_case_exprt : public binary_exprt
{
public:
  explicit sva_case_exprt(exprt __case_op, exprt __cases)
    : binary_exprt(
        std::move(__case_op),
        ID_sva_case,
        std::move(__cases),
        verilog_sva_property_typet{})
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

  exprt lower() const;

protected:
  using binary_exprt::op0;
  using binary_exprt::op1;
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

/// Base class for [->...], [*...], [=...]
/// The ... constraint may be blank, x, x:y, x:$
class sva_sequence_repetition_exprt : public ternary_exprt
{
public:
  /// number of repetitions not given, e.g., [*] or [+]
  sva_sequence_repetition_exprt(exprt __op, irep_idt __id)
    : ternary_exprt{
        __id,
        std::move(__op),
        nil_exprt{},
        nil_exprt{},
        verilog_sva_sequence_typet{}}
  {
  }

  /// fixed number of repetitions
  sva_sequence_repetition_exprt(
    exprt __op,
    irep_idt __id,
    constant_exprt __repetitions)
    : ternary_exprt{
        __id,
        std::move(__op),
        std::move(__repetitions),
        nil_exprt{},
        verilog_sva_sequence_typet{}}
  {
  }

  /// bounded range for the number of repetitions
  sva_sequence_repetition_exprt(
    exprt __op,
    irep_idt __id,
    constant_exprt __from,
    constant_exprt __to)
    : ternary_exprt{
        __id,
        std::move(__op),
        std::move(__from),
        std::move(__to),
        verilog_sva_sequence_typet{}}
  {
  }

  /// unbounded range for the number of repetitions
  sva_sequence_repetition_exprt(
    exprt __op,
    irep_idt __id,
    constant_exprt __from,
    infinity_exprt __to)
    : ternary_exprt{
        __id,
        std::move(__op),
        std::move(__from),
        std::move(__to),
        verilog_sva_sequence_typet{}}
  {
  }

  // May be a sequence for [*...], Boolean otherwise
  const exprt &op() const
  {
    return op0();
  }

  exprt &op()
  {
    return op0();
  }

  /// true if number of repetitions is given
  bool repetitions_given() const
  {
    return op1().is_not_nil();
  }

  /// op[*0] is a special case, denoting the empty match
  bool is_empty_match() const
  {
    return is_singleton() && op1().is_zero();
  }

  // The number of repetitions must be a constant after elaboration.
  const constant_exprt &repetitions() const
  {
    PRECONDITION(is_singleton());
    return static_cast<const constant_exprt &>(op1());
  }

  constant_exprt &repetitions()
  {
    PRECONDITION(is_singleton());
    return static_cast<constant_exprt &>(op1());
  }

  bool is_range() const
  {
    return op2().is_not_nil();
  }

  bool is_bounded_range() const
  {
    return op2().is_not_nil() && op2().id() != ID_infinity;
  }

  bool is_singleton() const
  {
    return op1().is_not_nil() && op2().is_nil();
  }

  bool is_unbounded() const
  {
    return op2().id() == ID_infinity;
  }

  const constant_exprt &from() const
  {
    PRECONDITION(is_range());
    return static_cast<const constant_exprt &>(op1());
  }

  constant_exprt &from()
  {
    PRECONDITION(is_range());
    return static_cast<constant_exprt &>(op1());
  }

  const constant_exprt &to() const
  {
    PRECONDITION(is_bounded_range());
    return static_cast<const constant_exprt &>(op2());
  }

  constant_exprt &to()
  {
    PRECONDITION(is_bounded_range());
    return static_cast<constant_exprt &>(op2());
  }

protected:
  using ternary_exprt::op0;
  using ternary_exprt::op1;
  using ternary_exprt::op2;
};

inline const sva_sequence_repetition_exprt &
to_sva_sequence_repetition_expr(const exprt &expr)
{
  sva_sequence_repetition_exprt::check(expr);
  return static_cast<const sva_sequence_repetition_exprt &>(expr);
}

inline sva_sequence_repetition_exprt &
to_sva_sequence_repetition_expr(exprt &expr)
{
  sva_sequence_repetition_exprt::check(expr);
  return static_cast<sva_sequence_repetition_exprt &>(expr);
}

/// op[+]
class sva_sequence_repetition_plus_exprt : public sva_sequence_repetition_exprt
{
public:
  /// The operand is a sequence
  explicit sva_sequence_repetition_plus_exprt(exprt op)
    : sva_sequence_repetition_exprt{
        std::move(op),
        ID_sva_sequence_repetition_plus}
  {
  }

  // op[*1:$]
  exprt lower() const;
};

static inline const sva_sequence_repetition_plus_exprt &
to_sva_sequence_repetition_plus_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_repetition_plus);
  sva_sequence_repetition_plus_exprt::check(expr);
  return static_cast<const sva_sequence_repetition_plus_exprt &>(expr);
}

static inline sva_sequence_repetition_plus_exprt &
to_sva_sequence_repetition_plus_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_repetition_plus);
  sva_sequence_repetition_plus_exprt::check(expr);
  return static_cast<sva_sequence_repetition_plus_exprt &>(expr);
}

/// [*] or [*n] or [*x:y] or [*x:$]
class sva_sequence_repetition_star_exprt : public sva_sequence_repetition_exprt
{
public:
  /// op[*]
  explicit sva_sequence_repetition_star_exprt(exprt __op)
    : sva_sequence_repetition_exprt{
        std::move(__op),
        ID_sva_sequence_repetition_star}
  {
  }

  /// op[*n]
  sva_sequence_repetition_star_exprt(exprt __op, constant_exprt __repetitions)
    : sva_sequence_repetition_exprt{
        std::move(__op),
        ID_sva_sequence_repetition_star,
        std::move(__repetitions)}
  {
  }

  /// op[*x:y]
  sva_sequence_repetition_star_exprt(
    exprt __op,
    constant_exprt __from,
    constant_exprt __to)
    : sva_sequence_repetition_exprt{
        std::move(__op),
        ID_sva_sequence_repetition_star,
        std::move(__from),
        std::move(__to)}
  {
  }

  /// op[*x:$]
  sva_sequence_repetition_star_exprt(
    exprt __op,
    constant_exprt __from,
    infinity_exprt __to)
    : sva_sequence_repetition_exprt{
        std::move(__op),
        ID_sva_sequence_repetition_star,
        std::move(__from),
        std::move(__to)}
  {
  }

  /// [*] --> [0:$]
  /// [*n] --> op ##1 op ##1 op ...
  /// [*x:y] --> op[*x] or op[*x+1] or ... or op[*y]
  exprt lower() const;
};

inline const sva_sequence_repetition_star_exprt &
to_sva_sequence_repetition_star_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_repetition_star);
  sva_sequence_repetition_star_exprt::check(expr);
  return static_cast<const sva_sequence_repetition_star_exprt &>(expr);
}

inline sva_sequence_repetition_star_exprt &
to_sva_sequence_repetition_star_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_repetition_star);
  sva_sequence_repetition_star_exprt::check(expr);
  return static_cast<sva_sequence_repetition_star_exprt &>(expr);
}

class sva_sequence_goto_repetition_exprt : public sva_sequence_repetition_exprt
{
public:
  sva_sequence_goto_repetition_exprt(exprt __op, constant_exprt __repetitions)
    : sva_sequence_repetition_exprt{
        std::move(__op),
        ID_sva_sequence_goto_repetition,
        std::move(__repetitions)}
  {
  }
};

inline const sva_sequence_goto_repetition_exprt &
to_sva_sequence_goto_repetition_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_goto_repetition);
  sva_sequence_goto_repetition_exprt::check(expr);
  return static_cast<const sva_sequence_goto_repetition_exprt &>(expr);
}

inline sva_sequence_goto_repetition_exprt &
to_sva_sequence_goto_repetition_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_goto_repetition);
  sva_sequence_goto_repetition_exprt::check(expr);
  return static_cast<sva_sequence_goto_repetition_exprt &>(expr);
}

class sva_sequence_non_consecutive_repetition_exprt
  : public sva_sequence_repetition_exprt
{
public:
  sva_sequence_non_consecutive_repetition_exprt(
    exprt __op,
    constant_exprt __repetitions)
    : sva_sequence_repetition_exprt{
        std::move(__op),
        ID_sva_sequence_non_consecutive_repetition,
        std::move(__repetitions)}
  {
  }
};

inline const sva_sequence_non_consecutive_repetition_exprt &
to_sva_sequence_non_consecutive_repetition_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_non_consecutive_repetition);
  sva_sequence_non_consecutive_repetition_exprt::check(expr);
  return static_cast<const sva_sequence_non_consecutive_repetition_exprt &>(
    expr);
}

inline sva_sequence_non_consecutive_repetition_exprt &
to_sva_sequence_non_consecutive_repetition_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_non_consecutive_repetition);
  sva_sequence_non_consecutive_repetition_exprt::check(expr);
  return static_cast<sva_sequence_non_consecutive_repetition_exprt &>(expr);
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

class sva_sequence_within_exprt : public binary_exprt
{
public:
  sva_sequence_within_exprt(exprt op0, exprt op1)
    : binary_exprt(
        std::move(op0),
        ID_sva_sequence_within,
        std::move(op1),
        verilog_sva_sequence_typet{})
  {
  }
};

static inline const sva_sequence_within_exprt &
to_sva_sequence_within_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_within);
  sva_sequence_within_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_sequence_within_exprt &>(expr);
}

static inline sva_sequence_within_exprt &
to_sva_sequence_within_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_within);
  sva_sequence_within_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_sequence_within_exprt &>(expr);
}

class sva_sequence_throughout_exprt : public binary_exprt
{
public:
  sva_sequence_throughout_exprt(exprt op0, exprt op1)
    : binary_exprt(std::move(op0), ID_sva_sequence_throughout, std::move(op1))
  {
  }

  const exprt &sequence() const
  {
    return op1();
  }

  exprt &sequence()
  {
    return op1();
  }
};

static inline const sva_sequence_throughout_exprt &
to_sva_sequence_throughout_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_throughout);
  sva_sequence_throughout_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_sequence_throughout_exprt &>(expr);
}

static inline sva_sequence_throughout_exprt &
to_sva_sequence_throughout_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_throughout);
  sva_sequence_throughout_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_sequence_throughout_exprt &>(expr);
}

class sva_sequence_first_match_exprt : public binary_exprt
{
public:
  // the second operand is optional
  explicit sva_sequence_first_match_exprt(exprt op)
    : binary_exprt(std::move(op), ID_sva_sequence_first_match, nil_exprt{})
  {
  }

  sva_sequence_first_match_exprt(exprt op, exprt action)
    : binary_exprt(
        std::move(op),
        ID_sva_sequence_first_match,
        std::move(action))
  {
  }

  const exprt &sequence() const
  {
    return op0();
  }

  exprt &sequence()
  {
    return op0();
  }
};

static inline const sva_sequence_first_match_exprt &
to_sva_sequence_first_match_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_first_match);
  sva_sequence_first_match_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_sequence_first_match_exprt &>(expr);
}

static inline sva_sequence_first_match_exprt &
to_sva_sequence_first_match_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_first_match);
  sva_sequence_first_match_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_sequence_first_match_exprt &>(expr);
}

/// 1800-2017 16.12.2 Sequence property
/// Equivalent to weak(...) or strong(...) depending on context.
class sva_sequence_property_exprt : public sva_sequence_property_expr_baset
{
public:
  explicit sva_sequence_property_exprt(exprt op)
    : sva_sequence_property_expr_baset(ID_sva_sequence_property, std::move(op))
  {
  }
};

static inline const sva_sequence_property_exprt &
to_sva_sequence_property_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_property);
  sva_sequence_property_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<const sva_sequence_property_exprt &>(expr);
}

static inline sva_sequence_property_exprt &
to_sva_sequence_property_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_property);
  sva_sequence_property_exprt::check(expr, validation_modet::INVARIANT);
  return static_cast<sva_sequence_property_exprt &>(expr);
}

/// SVA sequences can be interpreted as weak or strong
enum class sva_sequence_semanticst
{
  WEAK,
  STRONG
};

/// a base class for both sequence and property instance expressions
class sva_sequence_property_instance_exprt : public ternary_exprt
{
public:
  sva_sequence_property_instance_exprt(
    symbol_exprt _symbol,
    exprt::operandst _arguments,
    verilog_sequence_property_declaration_baset _declaration)
    : ternary_exprt{
        ID_sva_sequence_property_instance,
        std::move(_symbol),
        multi_ary_exprt{ID_arguments, std::move(_arguments), typet{}},
        std::move(_declaration),
        typet{}}
  {
  }

  const symbol_exprt &symbol() const
  {
    return static_cast<const symbol_exprt &>(op0());
  }

  symbol_exprt &symbol()
  {
    return static_cast<symbol_exprt &>(op0());
  }

  exprt::operandst &arguments()
  {
    return op1().operands();
  }

  const exprt::operandst &arguments() const
  {
    return op1().operands();
  }

  verilog_sequence_property_declaration_baset &declaration()
  {
    return static_cast<verilog_sequence_property_declaration_baset &>(op2());
  }

  const verilog_sequence_property_declaration_baset &declaration() const
  {
    return static_cast<const verilog_sequence_property_declaration_baset &>(
      op2());
  }

  /// Add the source location from \p other, if it has any.
  sva_sequence_property_instance_exprt &&
  with_source_location(const exprt &other) &&
  {
    if(other.source_location().is_not_nil())
      add_source_location() = other.source_location();
    return std::move(*this);
  }
};

inline const sva_sequence_property_instance_exprt &
to_sva_sequence_property_instance_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_property_instance);
  sva_sequence_property_instance_exprt::check(expr);
  return static_cast<const sva_sequence_property_instance_exprt &>(expr);
}

inline sva_sequence_property_instance_exprt &
to_sva_sequence_property_instance_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sva_sequence_property_instance);
  sva_sequence_property_instance_exprt::check(expr);
  return static_cast<sva_sequence_property_instance_exprt &>(expr);
}

#endif
