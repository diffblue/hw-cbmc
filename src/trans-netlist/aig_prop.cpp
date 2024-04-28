/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "aig_prop.h"

#include <set>
#include <stack>

// Tries to compact AIGs corresponding to xor and equality
// Needed to match the performance of the native CNF back-end.
#define USE_AIG_COMPACT

// Use the Plaisted-Greenbaum encoding, again, needed to match the
// native CNF back-end.
#define USE_PG

literalt aig_prop_baset::land(const bvt &bv) {
  literalt literal = const_literal(true);

  // Introduces N-1 extra nodes for N bits
  // See convert_node for where this overhead is removed
  for(auto bv_lit : bv)
    literal = land(bv_lit, literal);

  return literal;
}

literalt aig_prop_baset::lor(const bvt &bv) {
  literalt literal = const_literal(true);

  // Introduces N-1 extra nodes for N bits
  // See convert_node for where this overhead is removed
  for(auto bv_lit : bv)
    literal = land(neg(bv_lit), literal);

  return neg(literal);
}

literalt aig_prop_baset::lxor(const bvt &bv) {
  literalt literal = const_literal(false);

  for(auto bv_lit : bv)
    literal = lxor(bv_lit, literal);

  return literal;
}

literalt aig_prop_baset::land(literalt a, literalt b) {
  if (a.is_true() || b.is_false())
    return b;
  if (b.is_true() || a.is_false())
    return a;

  if (a == neg(b))
    return const_literal(false);
  if (a == b)
    return a;

  return dest.new_and_node(a, b);
}

literalt aig_prop_baset::lor(literalt a, literalt b) {
  return neg(land(neg(a), neg(b))); // De Morgan's
}

literalt aig_prop_baset::lxor(literalt a, literalt b) {
  if (a.is_false())
    return b;
  if (b.is_false())
    return a;
  if (a.is_true())
    return neg(b);
  if (b.is_true())
    return neg(a);

  if (a == b)
    return const_literal(false);
  if (a == neg(b))
    return const_literal(true);

  // This produces up to three nodes!
  // See convert_node for where this overhead is removed
  return lor(land(a, neg(b)), land(neg(a), b));
}

literalt aig_prop_baset::lnand(literalt a, literalt b) { return !land(a, b); }

literalt aig_prop_baset::lnor(literalt a, literalt b) { return !lor(a, b); }

literalt aig_prop_baset::lequal(literalt a, literalt b) { return !lxor(a, b); }

literalt aig_prop_baset::limplies(literalt a, literalt b) {
  return lor(neg(a), b);
}

literalt aig_prop_baset::lselect(literalt a, literalt b,
                                 literalt c) { // a?b:c=(a AND b) OR (/a AND c)
  if (a.is_true())
    return b;
  if (a.is_false())
    return c;
  if (b == c)
    return b;

  // This produces unnecessary clauses and variables
  // See convert_node for where this overhead is removed

  return lor(land(a, b), land(neg(a), c));
}

void aig_prop_baset::set_equal(literalt a, literalt b) {
#ifdef USE_AIG_COMPACT
  // The compact encoding should reduce this
  l_set_to_true(lequal(a, b));

#else
  // we produce two constraints:
  // a|!b   !a|b

  l_set_to_true(lor(pos(a), neg(b)));
  l_set_to_true(lor(neg(a), pos(b)));
#endif
}
