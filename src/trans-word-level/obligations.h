/*******************************************************************\

Module: Unwinding the Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_WORD_LEVEL_OBLIGATIONS_H
#define CPROVER_TRANS_WORD_LEVEL_OBLIGATIONS_H

#include <util/expr.h>
#include <util/mp_arith.h>

#include <map>

class obligationst
{
public:
  obligationst() = default;

  explicit obligationst(const mp_integer &t, const exprt &expr)
  {
    add(t, expr);
  }

  explicit obligationst(const std::pair<mp_integer, exprt> &pair)
  {
    add(pair.first, pair.second);
  }

  // The value are conditions that must be met for the property to hold.
  // The key is the length of the counterexample if the condition is violated.
  std::map<mp_integer, exprt::operandst> map;

  // add a condition
  void add(const mp_integer &t, exprt expr)
  {
    map[t].push_back(std::move(expr));
  }

  void add(const std::pair<mp_integer, exprt::operandst> &pair)
  {
    auto &entry = map[pair.first];
    for(auto &expr : pair.second)
      entry.push_back(expr);
  }

  // add a set of conditions
  void add(const obligationst &obligations)
  {
    for(auto &obligation : obligations.map)
      add(obligation);
  }

  /// return the conjunction of all obligations,
  /// and the biggest of the timeframes involved
  std::pair<mp_integer, exprt> conjunction() const;
};

#endif
