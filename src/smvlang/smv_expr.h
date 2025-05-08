/*******************************************************************\

Module: SMV Expressions

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_SMV_EXPR_H
#define CPROVER_SMV_EXPR_H

#include <util/std_expr.h>

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

#endif // CPROVER_SMV_EXPR_H
