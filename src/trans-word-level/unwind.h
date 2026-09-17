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

#endif
