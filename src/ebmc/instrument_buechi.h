/*******************************************************************\

Module: Buechi Automaton Instrumentation

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Buechi Automaton Instrumentation

#ifndef EBMC_BUECHI_AUTOMATON_INSTRUMENTATION_H
#define EBMC_BUECHI_AUTOMATON_INSTRUMENTATION_H

#include <util/message.h>

#include "ebmc_properties.h"
#include "transition_system.h"

void instrument_buechi(
  transition_systemt &,
  ebmc_propertiest &,
  message_handlert &);

#endif // EBMC_BUECHI_AUTOMATON_INSTRUMENTATION_H
