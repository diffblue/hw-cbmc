/// Author: Diffblue Ltd.

/// \file
/// Hardware verification specific utilities

#ifndef HW_CBMC_UTIL_EBMC_UTIL_H
#define HW_CBMC_UTIL_EBMC_UTIL_H

#include <algorithm>

#include <util/arith_tools.h>
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

inline optionalt<std::pair<std::string, std::size_t>>
b2h_conversion_specs(const exprt &expr) {
  if (expr.id() == ID_constant) {
    auto &constant_expr = to_constant_expr(expr);
    const typet &type = constant_expr.type();
    if (type.id() == ID_unsignedbv || type.id() == ID_signedbv) {
      const std::size_t &width = to_bitvector_type(type).get_width();
      const std::string value = id2string(constant_expr.get_value());
      if (value.size() == width &&
          std::all_of(value.begin(), value.end(),
                      [](char c) { return (c == '0' || c == '1'); })) {
        return std::make_pair(value, width);
      }
    }
  }

  return {};
}

inline void binary_to_hex_reinterpret(exprt &expr) {
  auto conversion_specs = b2h_conversion_specs(expr);
  if (conversion_specs.has_value()) {
    expr.set(ID_value, integer2bvrep(string2integer(conversion_specs->first, 2),
                                     conversion_specs->second));
  }
}

inline exprt binary_to_hex(const exprt &expr) {
  auto conversion_specs = b2h_conversion_specs(expr);
  if (conversion_specs.has_value()) {
    return constant_exprt{
        integer2bvrep(string2integer(conversion_specs->first, 2),
                      conversion_specs->second),
        expr.type()};
  }

  return expr;
}

#endif // HW_CBMC_UTIL_EBMC_UTIL_H
