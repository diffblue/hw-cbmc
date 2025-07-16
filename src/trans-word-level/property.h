/*******************************************************************\

Module: Unwinding the Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_WORD_LEVEL_PROPERTY_WORD_LEVEL_H
#define CPROVER_TRANS_WORD_LEVEL_PROPERTY_WORD_LEVEL_H

#include <util/expr.h>
#include <util/message.h>
#include <util/mp_arith.h>

/// returns a vector of obligation expressions, one per timeframe
exprt::operandst property(
  const exprt &property_expr,
  message_handlert &,
  std::size_t no_timeframes);

/// Is the given property supported by word-level unwinding?
bool bmc_supports_property(const exprt &);

#endif
