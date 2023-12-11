/*******************************************************************\

Module: Data Structure for the Properties

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_PROPERTIES_H
#define CPROVER_EBMC_PROPERTIES_H

#include <util/cmdline.h>
#include <util/message.h>

#include <solvers/prop/literal.h>
#include <trans-netlist/trans_trace.h>
#include <trans-word-level/property.h>

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
      UNKNOWN,           // no work done yet
      DISABLED,          // turned off by user
      PROVED,            // property is true, unbounded
      PROVED_WITH_BOUND, // property is true, with bound
      REFUTED,           // property is false, possibly counterexample
      DROPPED,           // given up
      FAILURE,           // error during anaysis
      INCONCLUSIVE       // analysis can't determine truth
    } status = statust::UNKNOWN;

    std::size_t bound = 0;
    std::optional<trans_tracet> counterexample;

    bool has_counterexample() const
    {
      return counterexample.has_value();
    }

    bool is_unknown() const
    {
      return status == statust::UNKNOWN;
    }

    bool is_disabled() const
    {
      return status == statust::DISABLED;
    }

    bool is_proved() const
    {
      return status == statust::PROVED;
    }

    bool is_proved_with_bound() const
    {
      return status == statust::PROVED_WITH_BOUND;
    }

    bool is_refuted() const
    {
      return status == statust::REFUTED;
    }

    bool is_dropped() const
    {
      return status == statust::DROPPED;
    }

    bool is_failure() const
    {
      return status == statust::FAILURE;
    }

    bool is_inconclusive() const
    {
      return status == statust::INCONCLUSIVE;
    }

    void unknown()
    {
      status = statust::UNKNOWN;
    }

    void disable()
    {
      status = statust::DISABLED;
    }

    void proved()
    {
      status = statust::PROVED;
    }

    void proved_with_bound(std::size_t _bound)
    {
      status = statust::PROVED_WITH_BOUND;
      bound = _bound;
    }

    void refuted()
    {
      status = statust::REFUTED;
    }

    void drop()
    {
      status = statust::DROPPED;
    }

    void failure()
    {
      status = statust::FAILURE;
    }

    void inconclusive()
    {
      status = statust::INCONCLUSIVE;
    }

    std::string status_as_string() const;

    propertyt() = default;

    bool requires_lasso_constraints() const
    {
      return ::requires_lasso_constraints(expr);
    }
  };

  typedef std::list<propertyt> propertiest;
  propertiest properties;

  bool all_properties_proved() const
  {
    for(const auto &p : properties)
      if(!p.is_proved() && !p.is_proved_with_bound() && !p.is_disabled())
        return false;

    return true;
  }

  bool requires_lasso_constraints() const
  {
    for(const auto &p : properties)
      if(!p.is_disabled() && p.requires_lasso_constraints())
        return true;

    return false;
  }

  static ebmc_propertiest from_command_line(
    const cmdlinet &,
    const transition_systemt &,
    message_handlert &);

  static ebmc_propertiest
  from_transition_system(const transition_systemt &, message_handlert &);

  bool select_property(const cmdlinet &, message_handlert &);
};

#endif // CPROVER_EBMC_PROPERTIES_H
