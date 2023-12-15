/*******************************************************************\

Module: k-Induction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EBMC_K_INDUCTION_H
#define CPROVER_EBMC_K_INDUCTION_H

#include <util/cmdline.h>
#include <util/ui_message.h>

#include "ebmc_solver_factory.h"

int do_k_induction(const cmdlinet &, ui_message_handlert &);

class transition_systemt;
class ebmc_propertiest;

// Basic k-induction. The result is stored in the ebmc_propertiest argument.
void k_induction(
  std::size_t k,
  const transition_systemt &,
  ebmc_propertiest &,
  const ebmc_solver_factoryt &,
  message_handlert &);

#endif
