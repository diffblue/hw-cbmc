/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_UNWIND_H
#define CPROVER_TRANS_UNWIND_H

#include <util/mathematical_expr.h>
#include <util/message.h>
#include <util/std_expr.h>

// word-level

struct word_level_unwind_optionst
{
  /// assert the initial-state constraint (transt::init()) at timeframe 0
  bool add_initial_state = true;
  /// assert the in-state constraints (transt::invar())
  bool add_constraints = true;
};

void unwind(
  const transt &,
  message_handlert &,
  class decision_proceduret &,
  std::size_t no_timeframes,
  const class namespacet &,
  word_level_unwind_optionst options = {});

/// Adds the constraints for the timeframes
/// from_timeframe, ..., to_timeframe-1, i.e., the in-state constraints
/// for these timeframes and the transitions from each of them to its
/// successor. The initial-state constraint is added if from_timeframe
/// is zero. Calling this with 0..a and then a..b yields the same
/// constraints as a single call with 0..b, which enables incremental
/// unwinding.
void unwind(
  const transt &,
  message_handlert &,
  class decision_proceduret &,
  std::size_t from_timeframe,
  std::size_t to_timeframe,
  const class namespacet &,
  word_level_unwind_optionst options = {});

#endif
