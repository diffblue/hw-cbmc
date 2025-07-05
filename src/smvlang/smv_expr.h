/*******************************************************************\

Module: SMV Expressions

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_SMV_EXPR_H
#define CPROVER_SMV_EXPR_H

#include <util/std_expr.h>

class smv_abs_exprt : public unary_exprt
{
public:
  smv_abs_exprt(exprt __op, typet __type)
    : unary_exprt{ID_smv_abs, std::move(__op), std::move(__type)}
  {
  }
};

inline const smv_abs_exprt &to_smv_abs_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_abs);
  smv_abs_exprt::check(expr);
  return static_cast<const smv_abs_exprt &>(expr);
}

inline smv_abs_exprt &to_smv_abs_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_abs);
  smv_abs_exprt::check(expr);
  return static_cast<smv_abs_exprt &>(expr);
}

class smv_bool_exprt : public unary_exprt
{
public:
  smv_bool_exprt(exprt __op, typet __type)
    : unary_exprt{ID_smv_bool, std::move(__op), std::move(__type)}
  {
  }
};

inline const smv_bool_exprt &to_smv_bool_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_bool);
  smv_bool_exprt::check(expr);
  return static_cast<const smv_bool_exprt &>(expr);
}

inline smv_bool_exprt &to_smv_bool_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_bool);
  smv_bool_exprt::check(expr);
  return static_cast<smv_bool_exprt &>(expr);
}

class smv_resize_exprt : public binary_exprt
{
public:
  smv_resize_exprt(exprt __op, constant_exprt __size, typet __type)
    : binary_exprt{
        std::move(__op),
        ID_smv_resize,
        std::move(__size),
        std::move(__type)}
  {
  }

  smv_resize_exprt(exprt __op, std::size_t __size, typet);

  const exprt &op() const
  {
    return op0();
  }

  exprt &op()
  {
    return op0();
  }

  const constant_exprt &size() const
  {
    return static_cast<const constant_exprt &>(op1());
  }

  constant_exprt &size()
  {
    return static_cast<constant_exprt &>(op1());
  }

protected:
  using binary_exprt::op0;
  using binary_exprt::op1;
};

inline const smv_resize_exprt &to_smv_resize_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_resize);
  smv_resize_exprt::check(expr);
  return static_cast<const smv_resize_exprt &>(expr);
}

inline smv_resize_exprt &to_smv_resize_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_resize);
  smv_resize_exprt::check(expr);
  return static_cast<smv_resize_exprt &>(expr);
}

class smv_extend_exprt : public binary_exprt
{
public:
  smv_extend_exprt(exprt __op, constant_exprt __size, typet __type)
    : binary_exprt{
        std::move(__op),
        ID_smv_extend,
        std::move(__size),
        std::move(__type)}
  {
  }

  smv_extend_exprt(exprt __op, std::size_t __size, typet);

  const exprt &op() const
  {
    return op0();
  }

  exprt &op()
  {
    return op0();
  }

  const constant_exprt &size() const
  {
    return static_cast<const constant_exprt &>(op1());
  }

  constant_exprt &size()
  {
    return static_cast<constant_exprt &>(op1());
  }

protected:
  using binary_exprt::op0;
  using binary_exprt::op1;
};

inline const smv_extend_exprt &to_smv_extend_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_extend);
  smv_extend_exprt::check(expr);
  return static_cast<const smv_extend_exprt &>(expr);
}

inline smv_extend_exprt &to_smv_extend_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_extend);
  smv_extend_exprt::check(expr);
  return static_cast<smv_extend_exprt &>(expr);
}

class smv_max_exprt : public binary_exprt
{
public:
  smv_max_exprt(exprt __lhs, exprt __rhs)
    : binary_exprt{std::move(__lhs), ID_smv_max, std::move(__rhs)}
  {
  }
};

inline const smv_max_exprt &to_smv_max_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_max);
  smv_max_exprt::check(expr);
  return static_cast<const smv_max_exprt &>(expr);
}

inline smv_max_exprt &to_smv_max_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_max);
  smv_max_exprt::check(expr);
  return static_cast<smv_max_exprt &>(expr);
}

class smv_min_exprt : public binary_exprt
{
public:
  smv_min_exprt(exprt __lhs, exprt __rhs)
    : binary_exprt{std::move(__lhs), ID_smv_min, std::move(__rhs)}
  {
  }
};

inline const smv_min_exprt &to_smv_min_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_min);
  smv_min_exprt::check(expr);
  return static_cast<const smv_min_exprt &>(expr);
}

inline smv_min_exprt &to_smv_min_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_min);
  smv_min_exprt::check(expr);
  return static_cast<smv_min_exprt &>(expr);
}

class smv_unsigned_cast_exprt : public unary_exprt
{
public:
  smv_unsigned_cast_exprt(exprt __op, typet __type)
    : unary_exprt{ID_smv_unsigned_cast, std::move(__op), std::move(__type)}
  {
  }
};

inline const smv_unsigned_cast_exprt &
to_smv_unsigned_cast_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_unsigned_cast);
  smv_unsigned_cast_exprt::check(expr);
  return static_cast<const smv_unsigned_cast_exprt &>(expr);
}

inline smv_unsigned_cast_exprt &to_smv_unsigned_cast_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_unsigned_cast);
  smv_unsigned_cast_exprt::check(expr);
  return static_cast<smv_unsigned_cast_exprt &>(expr);
}

class smv_signed_cast_exprt : public unary_exprt
{
public:
  smv_signed_cast_exprt(exprt __op, typet __type)
    : unary_exprt{ID_smv_signed_cast, std::move(__op), std::move(__type)}
  {
  }
};

inline const smv_signed_cast_exprt &to_smv_signed_cast_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_signed_cast);
  smv_signed_cast_exprt::check(expr);
  return static_cast<const smv_signed_cast_exprt &>(expr);
}

inline smv_signed_cast_exprt &to_smv_signed_cast_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_signed_cast);
  smv_signed_cast_exprt::check(expr);
  return static_cast<smv_signed_cast_exprt &>(expr);
}

class smv_toint_exprt : public unary_exprt
{
public:
  smv_toint_exprt(exprt __op, typet __type)
    : unary_exprt{ID_smv_toint, std::move(__op), std::move(__type)}
  {
  }
};

inline const smv_toint_exprt &to_smv_toint_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_toint);
  smv_toint_exprt::check(expr);
  return static_cast<const smv_toint_exprt &>(expr);
}

inline smv_toint_exprt &to_smv_toint_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_toint);
  smv_toint_exprt::check(expr);
  return static_cast<smv_toint_exprt &>(expr);
}

class smv_word1_exprt : public unary_exprt
{
public:
  smv_word1_exprt(exprt __op, typet __type)
    : unary_exprt{ID_smv_word1, std::move(__op), std::move(__type)}
  {
  }
};

inline const smv_word1_exprt &to_smv_word1_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_word1);
  smv_word1_exprt::check(expr);
  return static_cast<const smv_word1_exprt &>(expr);
}

inline smv_word1_exprt &to_smv_word1_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_smv_word1);
  smv_word1_exprt::check(expr);
  return static_cast<smv_word1_exprt &>(expr);
}

#endif // CPROVER_SMV_EXPR_H
