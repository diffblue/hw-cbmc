/// Author: Diffblue Ltd.

/// \file
/// Hardware verification specific utilities

#ifndef HW_CBMC_UTIL_EBMC_UTIL_H
#define HW_CBMC_UTIL_EBMC_UTIL_H

#include <algorithm>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include <solvers/sat/cnf.h>

// This function is legacy, and will be gradually removed.
// Consider to_integer(constant_exprt, mp_integer &) or numerical_cast<mp_integer>(...).
inline bool to_integer_non_constant(const exprt &expr, mp_integer &int_value)
{
  if (!can_cast_expr<constant_exprt>(expr))
    return true;

  return to_integer(to_constant_expr(expr), int_value);
}

#endif // HW_CBMC_UTIL_EBMC_UTIL_H
