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
class transt;

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

/// BMC with a given bound considers the paths with bound + 1 states that
/// satisfy the constraints and the assumptions in every state. The results
/// are vacuous when there is no such path, which is possible only when a
/// state may have no successor that satisfies the constraints and the
/// assumptions, or when there may be no such initial state. Neither is the
/// case when there are no assumptions and when all constraints are
/// definitions, see \ref has_general_constraints.
bool may_have_dead_ends(const transt &, const ebmc_propertiest &);

/// Report that no path with the given bound satisfies the constraints and
/// the assumptions, which makes the results of BMC vacuous.
void report_no_path(std::size_t bound, message_handlert &);

#endif // EBMC_BMC_H
