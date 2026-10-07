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
/// When \p cone_of_influence is set, the transition system is reduced
/// to the cone of influence of the properties before unwinding.
[[nodiscard]] property_checker_resultt bmc(
  std::size_t bound,
  bool convert_only,
  bool bmc_with_assumptions,
  bool cone_of_influence,
  const transition_systemt &,
  const ebmc_propertiest &,
  const ebmc_solver_factoryt &,
  message_handlert &);

#endif // EBMC_BMC_H
