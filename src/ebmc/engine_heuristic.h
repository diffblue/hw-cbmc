/*******************************************************************\

Module: EBMC Heuristic Engine Selection

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_ENGINE_HEURISTIC_H
#define CPROVER_EBMC_ENGINE_HEURISTIC_H

#include "property_checker.h"

property_checker_resultt engine_heuristic(
  const cmdlinet &,
  transition_systemt &,
  ebmc_propertiest &,
  message_handlert &);

#endif // CPROVER_EBMC_ENGINE_HEURISTIC_H
