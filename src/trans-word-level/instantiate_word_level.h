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
  unsigned current, unsigned no_timeframes,
  const namespacet &);

std::string timeframe_identifier(
  unsigned timeframe,
  const irep_idt &identifier);

#endif
