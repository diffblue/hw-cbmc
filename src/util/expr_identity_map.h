/*******************************************************************\

Module: Maps keyed by the identity of shared expressions

Author: Kiro

\*******************************************************************/

#ifndef CPROVER_UTIL_EXPR_IDENTITY_MAP_H
#define CPROVER_UTIL_EXPR_IDENTITY_MAP_H

#include <util/expr.h>

#include <unordered_map>
#include <utility>

/// A map from expressions to values, keyed by the identity of the shared
/// node of the expression rather than by its structure. Expressions are
/// DAGs; a structural lookup hashes and compares them, which takes time
/// exponential in their depth when two equal expressions do not share
/// their nodes. A lookup by identity takes constant time. Expressions that
/// are equal but not shared are distinct keys, so a pass that caches its
/// results here does work linear in the number of distinct nodes.
template <typename valuet>
class expr_identity_mapt
{
public:
  /// The value for \p expr, or nullptr if there is none.
  const valuet *find(const exprt &expr) const
  {
    auto it = map.find(&expr.read());
    return it == map.end() ? nullptr : &it->second.second;
  }

  void insert(const exprt &expr, valuet value)
  {
    map.emplace(&expr.read(), std::make_pair(expr, std::move(value)));
  }

  void clear()
  {
    map.clear();
  }

private:
  // The key expression is kept, so that its node is not freed, and its
  // address not reused, while the entry exists.
  std::unordered_map<const void *, std::pair<exprt, valuet>> map;
};

#endif // CPROVER_UTIL_EXPR_IDENTITY_MAP_H
