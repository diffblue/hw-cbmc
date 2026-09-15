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

/// @param initial_state When set, the initial strate constraint is added.
/// @param constraints When set, in-state constraints
///        (transt::invar()) are added.
void unwind(
  const transt &,
  message_handlert &,
  class decision_proceduret &,
  std::size_t no_timeframes,
  const class namespacet &,
  bool initial_state = true,
  bool constraints = true);

#endif
