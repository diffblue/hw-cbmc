/*******************************************************************\

Module: Liveness Engine

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_LIVENESS_ENGINE_H
#define CPROVER_EBMC_LIVENESS_ENGINE_H

#include "property_checker.h"

property_checker_resultt liveness_engine(
  const cmdlinet &,
  transition_systemt &,
  ebmc_propertiest &,
  message_handlert &);

#endif
