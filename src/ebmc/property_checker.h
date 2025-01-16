/*******************************************************************\

Module: EBMC Property Checker

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_PROPERTY_CHECKER_H
#define CPROVER_EBMC_PROPERTY_CHECKER_H

#include "ebmc_properties.h"
#include "transition_system.h"

class property_checker_resultt
{
public:
  enum class statust
  {
    VERIFICATION_RESULT, // property status populated
    SUCCESS,             // exit without error, but no property status
    ERROR                // error
  } status;

  explicit property_checker_resultt(statust _status) : status(_status)
  {
  }

  // copy
  explicit property_checker_resultt(const ebmc_propertiest &_properties)
    : status(statust::VERIFICATION_RESULT), properties(_properties.properties)
  {
  }

  static property_checker_resultt error()
  {
    return property_checker_resultt{statust::ERROR};
  }

  static property_checker_resultt success()
  {
    return property_checker_resultt{statust::SUCCESS};
  }

  using propertyt = ebmc_propertiest::propertyt;
  using propertiest = ebmc_propertiest::propertiest;

  propertiest properties;

  bool all_properties_proved() const
  {
    for(const auto &p : properties)
    {
      if(p.is_assumption())
      {
        // ignore
      }
      else if(
        !p.is_proved() && !p.is_proved_with_bound() && !p.is_disabled() &&
        !p.is_assumed())
      {
        return false;
      }
    }

    return true;
  }

  bool has_unknown_property() const
  {
    for(const auto &p : properties)
      if(p.is_unknown())
        return true;

    return false;
  }

  // command-line tool exit code, depending on property status
  int exit_code() const;
};

property_checker_resultt property_checker(
  const cmdlinet &,
  transition_systemt &,
  ebmc_propertiest &,
  message_handlert &);

#endif
