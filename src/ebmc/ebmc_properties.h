/*******************************************************************\

Module: Data Structure for the Properties

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_PROPERTIES_H
#define CPROVER_EBMC_PROPERTIES_H

#include <trans-netlist/trans_trace.h>

#include <solvers/prop/literal.h>

#include <util/message.h>

#include "transition_system.h"

class ebmc_propertiest
{
public:
  struct propertyt
  {
  public:
    std::size_t number = 0;
    irep_idt name;
    source_locationt location;
    std::string expr_string;
    irep_idt mode;
    exprt expr;
    bvt timeframe_literals;             // bit level
    exprt::operandst timeframe_handles; // word level
    std::string description;

    enum class statust
    {
      DISABLED,
      SUCCESS,
      FAILURE,
      UNKNOWN
    } status = statust::UNKNOWN;

    trans_tracet counterexample;

    inline bool is_disabled() const
    {
      return status == statust::DISABLED;
    }

    inline bool is_failure() const
    {
      return status == statust::FAILURE;
    }

    inline void disable()
    {
      status = statust::DISABLED;
    }

    inline void make_failure()
    {
      status = statust::FAILURE;
    }

    inline void make_success()
    {
      status = statust::SUCCESS;
    }

    inline void make_unknown()
    {
      status = statust::UNKNOWN;
    }

    propertyt() = default;
  };

  typedef std::list<propertyt> propertiest;
  propertiest properties;

  bool property_failure() const
  {
    for(const auto &p : properties)
      if(p.is_failure())
        return true;

    return false;
  }

  static bool from_transition_system(
    const transition_systemt &,
    ebmc_propertiest &,
    message_handlert &);
};

#endif // CPROVER_EBMC_PROPERTIES_H
