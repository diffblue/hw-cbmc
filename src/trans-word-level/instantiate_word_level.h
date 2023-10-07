/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BMC_INSTANTIATE_WORD_LEVEL_H
#define CPROVER_BMC_INSTANTIATE_WORD_LEVEL_H

#include <solvers/prop/prop_conv.h>

#include <util/namespace.h>

exprt instantiate(
  const exprt &expr,
  std::size_t current,
  std::size_t no_timeframes,
  const namespacet &);

std::string
timeframe_identifier(std::size_t timeframe, const irep_idt &identifier);

#endif
