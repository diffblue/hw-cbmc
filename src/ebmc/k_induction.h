/*******************************************************************\

Module: k-Induction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EBMC_K_INDUCTION_H
#define CPROVER_EBMC_K_INDUCTION_H

#include <util/cmdline.h>
#include <util/message.h>

#include "ebmc_solver_factory.h"
#include "property_checker.h"

class transition_systemt;
class ebmc_propertiest;

[[nodiscard]] property_checker_resultt k_induction(
  const cmdlinet &,
  transition_systemt &,
  ebmc_propertiest &,
  message_handlert &);

// Basic k-induction, for given k and given solver.
[[nodiscard]] property_checker_resultt k_induction(
  std::size_t k,
  const transition_systemt &,
  const ebmc_propertiest &,
  const ebmc_solver_factoryt &,
  message_handlert &);

#endif
