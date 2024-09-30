/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BMC_INSTANTIATE_WORD_LEVEL_H
#define CPROVER_BMC_INSTANTIATE_WORD_LEVEL_H

#include <util/mp_arith.h>
#include <util/std_expr.h>

exprt instantiate(
  const exprt &expr,
  const mp_integer &current,
  const mp_integer &no_timeframes);

std::pair<mp_integer, exprt> instantiate_property(
  const exprt &,
  const mp_integer &current,
  const mp_integer &no_timeframes);

std::string
timeframe_identifier(const mp_integer &timeframe, const irep_idt &identifier);

symbol_exprt timeframe_symbol(const mp_integer &timeframe, symbol_exprt);

#endif
