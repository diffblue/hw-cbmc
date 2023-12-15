/*******************************************************************\

Module: Bounded Model Checking

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Bounded Model Checking

#ifndef EBMC_BMC_H
#define EBMC_BMC_H

#include "ebmc_properties.h"
#include "ebmc_solver_factory.h"

class exprt;
class transition_systemt;

/// This is word-level BMC.
void bmc(
  std::size_t bound,
  bool convert_only,
  const transition_systemt &,
  ebmc_propertiest &,
  const ebmc_solver_factoryt &,
  message_handlert &);

#endif // EBMC_BMC_H
