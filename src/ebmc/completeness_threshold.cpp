/*******************************************************************\

Module: Completeness Threshold

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "completeness_threshold.h"

property_checker_resultt completeness_threshold(
  const cmdlinet &cmdline,
  const transition_systemt &transition_system,
  const ebmc_propertiest &properties,
  const ebmc_solver_factoryt &solver_factory,
  message_handlert &message_handler)
{
  // copy
  auto properties_copy = properties;

  // Do BMC with two timeframes
  for(auto &property : properties_copy.properties)
  {
  }

  return property_checker_resultt{properties_copy};
}
