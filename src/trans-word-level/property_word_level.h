/*******************************************************************\

Module: Unwinding the Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_WORD_LEVEL_PROPERTY_WORD_LEVEL_H
#define CPROVER_TRANS_WORD_LEVEL_PROPERTY_WORD_LEVEL_H

#include <util/message.h>
#include <util/namespace.h>

#include <solvers/prop/prop_conv.h>

void property(
  const exprt &property_expr,
  bvt &prop_bv,
  message_handlert &,
  prop_convt &solver,
  unsigned no_timeframes,
  const namespacet &);

#endif
