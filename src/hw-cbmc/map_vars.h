/*******************************************************************\

Module: Variable Mapping HDL<->C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_MAP_VARS_H
#define CPROVER_CBMC_MAP_VARS_H

#include <iostream>

#include <symbol_table.h>
#include <message.h>

void map_vars(
  symbol_tablet &symbol_table,
  const irep_idt &module,
  expr_listt &constraints,
  message_handlert &message,
  unsigned no_timeframes);

#endif
