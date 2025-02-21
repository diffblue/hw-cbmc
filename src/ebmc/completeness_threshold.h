/*******************************************************************\

Module: Completeness Threshold

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_COMPLETENESS_THRESHOLD_H
#define CPROVER_EBMC_COMPLETENESS_THRESHOLD_H

#include <util/cmdline.h>
#include <util/message.h>

#include "ebmc_solver_factory.h"
#include "property_checker.h"

class transition_systemt;
class ebmc_propertiest;

[[nodiscard]] property_checker_resultt completeness_threshold(
  const cmdlinet &,
  const transition_systemt &,
  const ebmc_propertiest &,
  const ebmc_solver_factoryt &,
  message_handlert &);

#endif
