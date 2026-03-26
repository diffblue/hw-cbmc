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
      _is_pending(false),
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

  /// A pending match represents a sequence that may still complete beyond
  /// the verification bound. Under weak semantics, such matches are
  /// vacuously true; the sequence must not be evaluated further.
  bool is_pending() const
  {
    return _is_pending;
  }

protected:
  bool _is_empty_match;
  bool _is_pending;
  exprt _condition;

public:
  mp_integer end_time;

  static sequence_matcht empty_match(mp_integer end_time)
  {
    auto result = sequence_matcht{end_time, true_exprt{}};
    result._is_empty_match = true;
    return result;
  }

  /// A pending match carries no end time: it represents a sequence that
  /// may complete beyond the verification bound.
  static sequence_matcht pending_match(exprt condition)
  {
    auto result = sequence_matcht{0, std::move(condition)};
    result._is_pending = true;
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
