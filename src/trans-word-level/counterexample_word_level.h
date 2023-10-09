/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BMC_COUNTEREXAMPLE_WORD_LEVEL_H
#define CPROVER_BMC_COUNTEREXAMPLE_WORD_LEVEL_H

#include <util/namespace.h>
#include <util/message.h>

void show_counterexample(
  message_handlert &,
  const class decision_proceduret &solver,
  std::size_t no_timeframes,
  const namespacet &ns,
  const std::string &module);

#endif
