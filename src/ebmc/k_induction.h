/*******************************************************************\

Module: k-Induction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EBMC_K_INDUCTION_H
#define CPROVER_EBMC_K_INDUCTION_H

#include <util/cmdline.h>
#include <util/message.h>

#include "ebmc_solver_factory.h"

class transition_systemt;
class ebmc_propertiest;

int k_induction(
  const cmdlinet &,
  transition_systemt &,
  ebmc_propertiest &,
  message_handlert &);

// Basic k-induction. The result is stored in the ebmc_propertiest argument.
void k_induction(
  std::size_t k,
  const transition_systemt &,
  ebmc_propertiest &,
  const ebmc_solver_factoryt &,
  message_handlert &);

#endif
