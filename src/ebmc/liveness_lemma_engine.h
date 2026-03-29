/*******************************************************************\

Module: Liveness Lemma Engine

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_LIVENESS_LEMMA_ENGINE_H
#define CPROVER_EBMC_LIVENESS_LEMMA_ENGINE_H

#include "ebmc_solver_factory.h"
#include "property_checker.h"

[[nodiscard]] property_checker_resultt liveness_lemma_engine(
  const cmdlinet &,
  const transition_systemt &,
  ebmc_propertiest &,
  const ebmc_solver_factoryt &, // unused
  message_handlert &);

#endif // CPROVER_EBMC_LIVENESS_LEMMA_ENGINE_H
