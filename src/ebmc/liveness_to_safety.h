/*******************************************************************\

Module: Liveness to Safety Translation

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Liveness to Safety Translation

#ifndef EBMC_LIVENESS_TO_SAFETY_H
#define EBMC_LIVENESS_TO_SAFETY_H

#include "ebmc_properties.h"
#include "transition_system.h"

void liveness_to_safety(transition_systemt &, ebmc_propertiest &);

#endif // EBMC_LIVENESS_TO_SAFETY_H
