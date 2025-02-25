/*******************************************************************\

Module: Completeness Threshold

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_COMPLETENESS_THRESHOLD_H
#define CPROVER_EBMC_COMPLETENESS_THRESHOLD_H

#include "ebmc_solver_factory.h"
#include "property_checker.h"

class cmdlinet;
class ebmc_propertiest;
class message_handlert;
class transition_systemt;

[[nodiscard]] property_checker_resultt completeness_threshold(
  const cmdlinet &,
  const transition_systemt &,
  const ebmc_propertiest &,
  const ebmc_solver_factoryt &,
  message_handlert &);

#endif
