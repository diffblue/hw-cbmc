/*******************************************************************\

Module: Variable Mapping HDL<->C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_MAP_VARS_H
#define CPROVER_CBMC_MAP_VARS_H

#include <iostream>

#include <context.h>
#include <message.h>

void map_vars(
  contextt &context,
  const irep_idt &module,
  expr_listt &constraints,
  message_handlert &message,
  unsigned no_timeframes);

#endif
