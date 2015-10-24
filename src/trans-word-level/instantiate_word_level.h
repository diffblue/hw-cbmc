/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BMC_INSTANTIATE_WORD_LEVEL_H
#define CPROVER_BMC_INSTANTIATE_WORD_LEVEL_H

#include <solvers/prop/prop_conv.h>

void instantiate(
  decision_proceduret &decision_procedure,
  const exprt &expr,
  unsigned current, unsigned no_timeframes,
  const namespacet &);

literalt instantiate_convert(
  prop_convt &prop_conv,
  const exprt &expr,
  unsigned current,
  const namespacet &);

void instantiate(
  exprt &expr,
  unsigned current, unsigned no_timeframes,
  const namespacet &);

std::string timeframe_identifier(
  unsigned timeframe,
  const irep_idt &identifier);

#endif
