/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BMC_INSTANTIATE_WORD_LEVEL_H
#define CPROVER_BMC_INSTANTIATE_WORD_LEVEL_H

#include <util/mp_arith.h>
#include <util/namespace.h>

#include <solvers/prop/prop_conv.h>

exprt instantiate(
  const exprt &expr,
  const mp_integer &current,
  const mp_integer &no_timeframes,
  const namespacet &);

std::string
timeframe_identifier(const mp_integer &timeframe, const irep_idt &identifier);

symbol_exprt timeframe_symbol(const mp_integer &timeframe, symbol_exprt);

#endif
