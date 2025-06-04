/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BMC_INSTANTIATE_WORD_LEVEL_H
#define CPROVER_BMC_INSTANTIATE_WORD_LEVEL_H

#include <util/mp_arith.h>
#include <util/std_expr.h>

// Instantiate a expression in the given time frame.
// May contain next_symbol, but must not contain any temporal operators.
exprt instantiate(
  const exprt &expr,
  const mp_integer &current,
  const mp_integer &no_timeframes);

// Instantiate an atomic state predicate in the given time frame.
// Must not contain next_symbol or any temporal operators.
exprt instantiate_property(
  const exprt &,
  const mp_integer &current,
  const mp_integer &no_timeframes);

std::string
timeframe_identifier(const mp_integer &timeframe, const irep_idt &identifier);

// Instantiate a symbol in the given time frame.
symbol_exprt timeframe_symbol(const mp_integer &timeframe, symbol_exprt);

#endif
