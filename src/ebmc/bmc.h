/*******************************************************************\

Module: Bounded Model Checking

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Bounded Model Checking

#ifndef EBMC_BMC_H
#define EBMC_BMC_H

#include "ebmc_solver_factory.h"
#include "property_checker.h"

class exprt;
class transition_systemt;

/// This is word-level BMC.
[[nodiscard]] property_checker_resultt bmc(
  std::size_t bound,
  bool convert_only,
  bool bmc_with_assumptions,
  const transition_systemt &,
  const ebmc_propertiest &,
  const ebmc_solver_factoryt &,
  message_handlert &);

#endif // EBMC_BMC_H
