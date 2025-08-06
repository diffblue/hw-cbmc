/*******************************************************************\

Module: Property Tautology Check

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_TAUTOLOGY_CHECK_H
#define CPROVER_EBMC_TAUTOLOGY_CHECK_H

#include "ebmc_solver_factory.h"
#include "property_checker.h"

class cmdlinet;
class ebmc_propertiest;
class message_handlert;

[[nodiscard]] property_checker_resultt tautology_check(
  const cmdlinet &,
  const ebmc_propertiest &,
  const ebmc_solver_factoryt &,
  message_handlert &);

#endif
