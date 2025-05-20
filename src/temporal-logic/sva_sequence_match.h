/*******************************************************************\

Module: SVA Sequence Matches

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGICS_SVA_SEQUENCE_MATCH_H
#define CPROVER_TEMPORAL_LOGICS_SVA_SEQUENCE_MATCH_H

#include <util/expr.h>
#include <util/mp_arith.h>

// A sequence of match conditions for potential matches of SVA
// sequence expressions.
struct sva_sequence_matcht
{
  // the empty match
  sva_sequence_matcht()
  {
  }

  // a match of length 1
  explicit sva_sequence_matcht(exprt __cond) : cond_vector{1, std::move(__cond)}
  {
  }

  std::vector<exprt> cond_vector;

  std::size_t length()
  {
    return cond_vector.size();
  }

  bool empty_match() const
  {
    return cond_vector.empty();
  }

  // generate true ##1 ... ##1 true with length n
  static sva_sequence_matcht true_match(const mp_integer &n);
};

// the set of potential matches for the given sequence expression
std::vector<sva_sequence_matcht> LTL_sequence_matches(const exprt &);

#endif // CPROVER_TEMPORAL_LOGICS_SVA_SEQUENCE_MATCH_H
