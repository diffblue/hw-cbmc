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

[[nodiscard]] property_checker_resultt tautology_check_engine(
  const cmdlinet &,           // unused
  const transition_systemt &, // unused
  const ebmc_propertiest &properties,
  const ebmc_solver_factoryt &solver,
  message_handlert &message_handler)
{
  return tautology_check(properties, solver, message_handler);
}

// Basic 1-induction for given solver
[[nodiscard]] property_checker_resultt one_induction_engine(
  const cmdlinet &, // unused
  const transition_systemt &transition_system,
  const ebmc_propertiest &properties,
  const ebmc_solver_factoryt &solver,
  message_handlert &message_handler)
{
  return k_induction(1, transition_system, properties, solver, message_handler);
}

// BMC with bound 5
[[nodiscard]] property_checker_resultt bmc_bound_5_engine(
  const cmdlinet &cmdline,
  const transition_systemt &transition_system,
  const ebmc_propertiest &properties,
  const ebmc_solver_factoryt &solver,
  message_handlert &message_handler)
{
  return bmc(
    5,     // bound
    false, // convert_only
    cmdline.isset("bmc-with-assumptions"),
    transition_system,
    properties,
    solver,
    message_handler);
}

struct enginet
{
  // the function to call
  std::function<property_checker_resultt(
    const cmdlinet &,
    transition_systemt &,
    ebmc_propertiest &,
    ebmc_solver_factoryt &,
    message_handlert &)>
    f;

  // a descriptive name
  const std::string name;
};

// engines to try, in given order
const enginet engines[] = {
  {tautology_check_engine, "tautology check"},
  {completeness_threshold, "completeness threshold"},
  {one_induction_engine, "one induction"},
  {bmc_bound_5_engine, "BMC with bound 5"},
};

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

  if(!properties.has_unfinished_property())
    return property_checker_resultt{properties}; // done

  message.status() << "No engine given, attempting heuristic engine selection"
                   << messaget::eom;

  auto solver_factory = ebmc_solver_factory(cmdline);

  // try engines in given order
  for(auto &engine : engines)
  {
    message.status() << "Attempting " << engine.name << messaget::eom;

    auto result = engine.f(
      cmdline, transition_system, properties, solver_factory, message_handler);

    properties.properties = result.properties;

    if(!properties.has_unfinished_property())
      return result; // done

    properties.reset_failure();
    properties.reset_inconclusive();
    properties.reset_unsupported();
  }

  // Give up
  return property_checker_resultt{properties}; // done
}
