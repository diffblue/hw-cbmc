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

/// This is incremental word-level BMC. The bounds 0, 1, ..., max_bound
/// are checked in order, using a single solver instance, and each
/// property is checked until it is decided. Refuted properties get a
/// shortest counterexample; the remaining properties are reported as
/// proved up to \p max_bound. Requires a SAT-based solver.
[[nodiscard]] property_checker_resultt bmc_incremental(
  std::size_t max_bound,
  bool bmc_with_assumptions,
  bool cone_of_influence,
  const transition_systemt &,
  const ebmc_propertiest &,
  const ebmc_solver_factoryt &,
  message_handlert &);

#endif // EBMC_BMC_H
