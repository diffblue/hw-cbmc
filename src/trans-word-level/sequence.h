/*******************************************************************\

Module: Encoding SVA sequences

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_WORD_LEVEL_SEQUENCE_H
#define CPROVER_TRANS_WORD_LEVEL_SEQUENCE_H

#include <util/expr.h>
#include <util/mp_arith.h>

/// A match for an SVA sequence.
class sequence_matcht
{
public:
  sequence_matcht(mp_integer __end_time, exprt __condition)
    : end_time(std::move(__end_time)), condition(std::move(__condition))
  {
  }

  mp_integer end_time;
  exprt condition;
};

/// A set of matches of an SVA sequence.
using sequence_matchest = std::vector<sequence_matcht>;

/// Returns a list of match points and matching conditions
/// for the given sequence expression starting at time t
[[nodiscard]] sequence_matchest instantiate_sequence(
  exprt expr,
  const mp_integer &t,
  const mp_integer &no_timeframes);

#endif // CPROVER_TRANS_WORD_LEVEL_SEQUENCE_H
