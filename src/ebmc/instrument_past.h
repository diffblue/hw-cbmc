/*******************************************************************\

Module: $past Instrumentation

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// $past Instrumentation

#ifndef EBMC_INSTRUMENT_PAST_H
#define EBMC_INSTRUMENT_PAST_H

#include "ebmc_properties.h"
#include "transition_system.h"

void instrument_past(transition_systemt &, ebmc_propertiest &);

#endif // EBMC_INSTRUMENT_PAST_H
