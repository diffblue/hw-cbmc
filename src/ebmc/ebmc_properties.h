/*******************************************************************\

Module: Data Structure for the Properties

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_PROPERTIES_H
#define CPROVER_EBMC_PROPERTIES_H

#include <util/cmdline.h>
#include <util/message.h>

#include <solvers/prop/literal.h>
#include <temporal-logic/temporal_logic.h>
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
    irep_idt identifier, name;
    source_locationt location;
    irep_idt mode;
    exprt original_expr;
    exprt normalized_expr;
    bvt timeframe_literals;             // bit level
    exprt::operandst timeframe_handles; // word level
    std::string description;

    enum class statust
    {
      UNKNOWN,            // no work done yet
      DISABLED,           // turned off by user
      ASSUMED,            // property is assumed to be true, unbounded
      UNSUPPORTED,        // property is unsupported
      PROVED,             // property is true, unbounded
      PROVED_WITH_BOUND,  // property is true, with bound
      REFUTED,            // property is false, possibly counterexample
      REFUTED_WITH_BOUND, // property is false, with bound
      DROPPED,            // given up
      FAILURE,            // error during anaysis
      INCONCLUSIVE        // analysis can't determine truth
    } status = statust::UNKNOWN;

    std::size_t bound = 0;
    std::optional<trans_tracet> witness_trace;
    std::optional<std::string> failure_reason;
    std::optional<std::string> proof_via;

    bool has_witness_trace() const
    {
      return witness_trace.has_value();
    }

    bool is_unknown() const
    {
      return status == statust::UNKNOWN;
    }

    bool is_disabled() const
    {
      return status == statust::DISABLED;
    }

    bool is_assumed() const
    {
      return status == statust::ASSUMED;
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

    bool is_unsupported() const
    {
      return status == statust::UNSUPPORTED;
    }

    bool is_inconclusive() const
    {
      return status == statust::INCONCLUSIVE;
    }

    void assumed()
    {
      status = statust::ASSUMED;
      failure_reason = {};
      proof_via = {};
    }

    void unknown()
    {
      status = statust::UNKNOWN;
      failure_reason = {};
      proof_via = {};
    }

    void disable()
    {
      status = statust::DISABLED;
      failure_reason = {};
      proof_via = {};
    }

    void proved()
    {
      status = statust::PROVED;
      failure_reason = {};
      proof_via = {};
    }

    void proved(std::string _proof_via)
    {
      status = statust::PROVED;
      failure_reason = {};
      proof_via = std::move(_proof_via);
    }

    void proved_with_bound(std::size_t _bound)
    {
      status = statust::PROVED_WITH_BOUND;
      bound = _bound;
      proof_via = {};
    }

    void refuted()
    {
      status = statust::REFUTED;
      failure_reason = {};
      proof_via = {};
    }

    void refuted_with_bound(std::size_t _bound)
    {
      status = statust::REFUTED_WITH_BOUND;
      bound = _bound;
      failure_reason = {};
      proof_via = {};
    }

    void drop()
    {
      status = statust::DROPPED;
      failure_reason = {};
      proof_via = {};
    }

    void failure(const std::optional<std::string> &reason = {})
    {
      status = statust::FAILURE;
      failure_reason = reason;
      proof_via = {};
    }

    void unsupported(const std::optional<std::string> &reason = {})
    {
      status = statust::UNSUPPORTED;
      failure_reason = reason;
      proof_via = {};
    }

    void inconclusive()
    {
      status = statust::INCONCLUSIVE;
      failure_reason = {};
      proof_via = {};
    }

    std::string status_as_string() const;

    propertyt() = default;

    bool requires_lasso_constraints() const
    {
      return ::requires_lasso_constraints(normalized_expr);
    }

    bool is_exists_path() const
    {
      return ::is_exists_path(original_expr);
    }

    bool is_assumption() const
    {
      return original_expr.id() == ID_sva_assume;
    }
  };

  typedef std::list<propertyt> propertiest;
  propertiest properties;

  bool has_unfinished_property() const
  {
    for(const auto &p : properties)
    {
      if(p.is_assumption())
      {
      }
      else if(
        p.is_unknown() || p.is_unsupported() || p.is_failure() ||
        p.is_inconclusive())
      {
        return true;
      }
    }

    return false;
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

  /// Implements --property ID.
  /// Throws when given an unknown identifier.
  void select_property(const cmdlinet &, message_handlert &);

  /// a map from property identifier to normalized expression
  std::map<irep_idt, exprt> make_property_map() const
  {
    std::map<irep_idt, exprt> result;
    for(auto &p : properties)
      if(!p.is_disabled())
        result.emplace(p.identifier, p.normalized_expr);
    return result;
  }

  /// Resets properties/assumptions in FAILURE state to
  /// ASSUMED/UNKNOWN respectively.
  void reset_failure()
  {
    for(auto &p : properties)
      if(p.is_failure())
      {
        if(p.is_assumption())
          p.assumed();
        else
          p.unknown();
      }
  }

  /// Resets properties in INCONCLUSIVE state to UNKNOWN.
  void reset_inconclusive()
  {
    for(auto &p : properties)
      if(p.is_inconclusive())
        p.unknown();
  }

  /// Resets properties in UNSUPPORTED state to UNKNOWN/ASSUMED.
  void reset_unsupported()
  {
    for(auto &p : properties)
      if(p.is_unsupported())
      {
        if(p.is_assumption())
          p.assumed();
        else
          p.unknown();
      }
  }
};

#endif // CPROVER_EBMC_PROPERTIES_H
