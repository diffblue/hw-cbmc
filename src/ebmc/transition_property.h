/*******************************************************************\

Module: Transition Property Engine

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_TRANSITION_PROPERTY_H
#define CPROVER_EBMC_TRANSITION_PROPERTY_H

#include "ebmc_solver_factory.h"
#include "property_checker.h"

class ebmc_propertiest;
class message_handlert;
class transition_systemt;

/// Proves properties that are relations between current and next
/// state pairs by checking whether they are implied by the
/// transition relation.
[[nodiscard]] property_checker_resultt transition_property(
  const transition_systemt &,
  const ebmc_propertiest &,
  const ebmc_solver_factoryt &,
  message_handlert &);

#endif // CPROVER_EBMC_TRANSITION_PROPERTY_H
