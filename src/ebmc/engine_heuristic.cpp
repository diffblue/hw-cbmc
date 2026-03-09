/*******************************************************************\

Module: EBMC Heuristic Engine Selection

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "engine_heuristic.h"

#include "bmc.h"
#include "completeness_threshold.h"
#include "ebmc_solver_factory.h"
#include "k_induction.h"
#include "tautology_check.h"

property_checker_resultt engine_heuristic(
  const cmdlinet &cmdline,
  transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  if(properties.properties.empty())
  {
    message.error() << "no properties" << messaget::eom;
    return property_checker_resultt::error();
  }

  auto solver_factory = ebmc_solver_factory(cmdline);

  if(!properties.has_unfinished_property())
    return property_checker_resultt{properties}; // done

  message.status() << "No engine given, attempting heuristic engine selection"
                   << messaget::eom;

  // First check if we can tell that the property is a tautology
  message.status() << "Tautology check" << messaget::eom;

  auto tautology_check_result =
    tautology_check(cmdline, properties, solver_factory, message_handler);

  properties.properties = tautology_check_result.properties;

  if(!properties.has_unfinished_property())
    return tautology_check_result; // done

  properties.reset_failure();
  properties.reset_inconclusive();
  properties.reset_unsupported();

  // Check whether we have a low completenes threshold
  message.status() << "Attempting completeness threshold" << messaget::eom;

  auto completeness_threshold_result = completeness_threshold(
    cmdline, transition_system, properties, solver_factory, message_handler);

  properties.properties = completeness_threshold_result.properties;

  if(!properties.has_unfinished_property())
    return completeness_threshold_result; // done

  properties.reset_failure();
  properties.reset_inconclusive();
  properties.reset_unsupported();

  // Now try 1-induction, word-level
  message.status() << "Attempting 1-induction" << messaget::eom;

  auto k_induction_result = k_induction(
    1, transition_system, properties, solver_factory, message_handler);

  properties.properties = k_induction_result.properties;

  if(!properties.has_unfinished_property())
    return k_induction_result; // done

  properties.reset_failure();
  properties.reset_inconclusive();
  properties.reset_unsupported();

  // Now try BMC with bound 5, word-level
  message.status() << "Attempting BMC with bound 5" << messaget::eom;

  auto bmc_result = bmc(
    5,     // bound
    false, // convert_only
    cmdline.isset("bmc-with-assumptions"),
    transition_system,
    properties,
    solver_factory,
    message_handler);

  properties.properties = std::move(bmc_result.properties);

  if(!properties.has_unfinished_property())
    return property_checker_resultt{properties}; // done

  properties.reset_failure();

  // Give up
  return property_checker_resultt{properties}; // done
}
