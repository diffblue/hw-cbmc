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
  // a match of length 1
  explicit sva_sequence_matcht(exprt __cond) : cond_vector{1, std::move(__cond)}
  {
  }

  // a match with given sequence of conditions
  explicit sva_sequence_matcht(std::vector<exprt> __cond_vector)
    : cond_vector(std::move(__cond_vector))
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

  bool operator==(const sva_sequence_matcht &other) const
  {
    return cond_vector == other.cond_vector;
  }
};

class sva_sequence_match_unsupportedt
{
public:
  explicit sva_sequence_match_unsupportedt(exprt __expr)
    : expr(std::move(__expr))
  {
  }

  exprt expr;
};

/// The set of potential matches for the given sequence expression.
/// Throws sva_sequence_match_unsupportedt when given sequence that cannot be translated.
std::vector<sva_sequence_matcht> LTL_sequence_matches(const exprt &);

#endif // CPROVER_TEMPORAL_LOGICS_SVA_SEQUENCE_MATCH_H
