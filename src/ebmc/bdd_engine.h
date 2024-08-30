/*******************************************************************\

Module: BDD Engine

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EBMC_BDD_ENGINE_H
#define CPROVER_EBMC_BDD_ENGINE_H

#include "property_checker.h"

property_checker_resultt bdd_engine(
  const cmdlinet &,
  transition_systemt &,
  ebmc_propertiest &,
  message_handlert &);

#endif
