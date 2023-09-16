/*******************************************************************\

Module: Variable Mapping HDL<->C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_MAP_VARS_H
#define CPROVER_CBMC_MAP_VARS_H

#include <util/message.h>
#include <util/symbol_table_base.h>

void map_vars(
  symbol_table_baset &,
  const irep_idt &module,
  std::list<exprt> &constraints,
  message_handlert &message,
  unsigned no_timeframes);

#endif
