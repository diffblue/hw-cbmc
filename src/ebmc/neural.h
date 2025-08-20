/*******************************************************************\

Module: Neural Engine

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_NEURAL_H
#define CPROVER_EBMC_NEURAL_H

#include <util/cmdline.h>
#include <util/message.h>

#include "ebmc_solver_factory.h"
#include "property_checker.h"

class transition_systemt;
class ebmc_propertiest;

[[nodiscard]] property_checker_resultt neural(
  const cmdlinet &,
  transition_systemt &,
  ebmc_propertiest &,
  message_handlert &);

#endif // CPROVER_EBMC_NEURAL_H
