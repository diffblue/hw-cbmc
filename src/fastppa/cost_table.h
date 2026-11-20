/*******************************************************************\

Module: FastPPA operator cost tables

Author: Kiro

\*******************************************************************/

#ifndef CPROVER_FASTPPA_COST_TABLE_H
#define CPROVER_FASTPPA_COST_TABLE_H

#include <iosfwd>
#include <map>
#include <string>

/// How a cost grows with the operand width w and, for array accesses,
/// the number of array elements n.
enum class cost_formt
{
  ONE,   // 1
  W,     // w
  LOGW,  // log2(w)
  WLOGW, // w * log2(w)
  W2,    // w^2
  N,     // n
  LOGN,  // log2(n)
  WN,    // w * n
  WN1    // w * (n - 1)
};

/// Throws ebmc_errort for unknown names.
cost_formt cost_form_from_string(const std::string &);
std::string to_string(cost_formt);
double evaluate(cost_formt, std::size_t w, std::size_t n);

/// The cost of one operator kind:
///   area  = a0 + a1 * area_form(w, n)   [um2]
///   delay = d0 + d1 * delay_form(w, n)  [ps]
struct cost_functiont
{
  cost_formt area_form = cost_formt::W;
  double a0 = 0, a1 = 0;
  cost_formt delay_form = cost_formt::ONE;
  double d0 = 0, d1 = 0;

  double area(std::size_t w, std::size_t n = 0) const
  {
    return a0 + a1 * evaluate(area_form, w, n);
  }

  double delay(std::size_t w, std::size_t n = 0) const
  {
    return d0 + d1 * evaluate(delay_form, w, n);
  }
};

/// The cost functions of all operator kinds for one technology. The
/// tables are fitted by benchmarking/fastppa_eval/fit.py on designs that
/// contain a single operator each.
class cost_tablet
{
public:
  /// The table in the format written by fit.py; throws ebmc_errort on
  /// errors.
  static cost_tablet from_stream(std::istream &, const std::string &name);
  static cost_tablet from_file(const std::string &file_name);

  /// A table compiled into fastppa; throws ebmc_errort if there is none
  /// with this name.
  static cost_tablet builtin(const std::string &name);

  /// Throws ebmc_errort if \p kind is not in the table.
  const cost_functiont &operator()(const std::string &kind) const;

protected:
  std::map<std::string, cost_functiont> table;
};

#endif // CPROVER_FASTPPA_COST_TABLE_H
