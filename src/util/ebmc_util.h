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

template <typename F>
void for_all_module_symbols(const symbol_tablet &symbol_table,
                            const irep_idt &module_name, F &&f) {
  using symbol_pairt = typename symbol_tablet::iteratort::value_type;
  std::for_each(symbol_table.begin(), symbol_table.end(),
                [&module_name, &f](const symbol_pairt &symbol_pair) {
                  const auto &symbol = symbol_pair.second;
                  if (symbol.module == module_name)
                    f(symbol);
                });
}

// This function is legacy, and will be gradually removed.
// Consider to_integer(constant_exprt, mp_integer &) or numerical_cast<mp_integer>(...).
inline bool to_integer_non_constant(const exprt &expr, mp_integer &int_value)
{
  if (!can_cast_expr<constant_exprt>(expr))
    return true;

  return to_integer(to_constant_expr(expr), int_value);
}

inline void cnf_gate_and(cnft &cnf, literalt a, literalt b, literalt o) {
  // a*b=c <==> (a + o')( b + o')(a'+b'+o)
  bvt lits(2);

  lits[0] = pos(a);
  lits[1] = neg(o);
  cnf.lcnf(lits);

  lits[0] = pos(b);
  lits[1] = neg(o);
  cnf.lcnf(lits);

  lits.clear();
  lits.reserve(3);
  lits.push_back(neg(a));
  lits.push_back(neg(b));
  lits.push_back(pos(o));
  cnf.lcnf(lits);
}

#endif // HW_CBMC_UTIL_EBMC_UTIL_H
