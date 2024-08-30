/*******************************************************************\

Module: EBMC Property Checker

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_PROPERTY_CHECKER_H
#define CPROVER_EBMC_PROPERTY_CHECKER_H

#include "ebmc_properties.h"
#include "transition_system.h"

enum class property_checker_resultt
{
  VERIFICATION_RESULT,
  SUCCESS,
  ERROR
};

int property_checker(
  const cmdlinet &,
  transition_systemt &,
  ebmc_propertiest &,
  message_handlert &);

#endif
