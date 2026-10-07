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
  const transition_systemt &,
  ebmc_propertiest &,
  message_handlert &);

// Basic k-induction, for given k and given solver.
// When cone_of_influence is set, the transition system is reduced
// to the cone of influence of the properties.
[[nodiscard]] property_checker_resultt k_induction(
  std::size_t k,
  bool cone_of_influence,
  const transition_systemt &,
  const ebmc_propertiest &,
  const ebmc_solver_factoryt &,
  message_handlert &);

#endif
