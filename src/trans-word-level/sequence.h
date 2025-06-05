/*******************************************************************\

Module: Encoding SVA sequences

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_WORD_LEVEL_SEQUENCE_H
#define CPROVER_TRANS_WORD_LEVEL_SEQUENCE_H

#include <util/expr.h>
#include <util/mp_arith.h>

#include <verilog/sva_expr.h>

/// A match for an SVA sequence.
class sequence_matcht
{
public:
  sequence_matcht(mp_integer __end_time, exprt __condition)
    : _is_empty_match(false),
      _condition(std::move(__condition)),
      end_time(std::move(__end_time))
  {
  }

  exprt condition() const
  {
    return _condition;
  }

  bool empty_match() const
  {
    return _is_empty_match;
  }

protected:
  bool _is_empty_match;
  exprt _condition;

public:
  mp_integer end_time;

  static sequence_matcht empty_match(mp_integer end_time)
  {
    auto result = sequence_matcht{end_time, true_exprt{}};
    result._is_empty_match = true;
    return result;
  }
};

/// A set of matches of an SVA sequence.
using sequence_matchest = std::vector<sequence_matcht>;

/// Returns a list of match points and matching conditions
/// for the given sequence expression starting at time t
[[nodiscard]] sequence_matchest instantiate_sequence(
  exprt expr,
  sva_sequence_semanticst,
  const mp_integer &t,
  const mp_integer &no_timeframes);

#endif // CPROVER_TRANS_WORD_LEVEL_SEQUENCE_H
