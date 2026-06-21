/*******************************************************************\

Module: Verilog Synthesis (Behavioral)

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Behavioral synthesis state: value maps, call frames, and loop
/// frames used during the synthesis of procedural statements.

#ifndef CPROVER_VERILOG_SYNTHESIS_BEHAVIORAL_H
#define CPROVER_VERILOG_SYNTHESIS_BEHAVIORAL_H

#include <util/mathematical_expr.h>
#include <util/std_expr.h>

#include <map>
#include <optional>
#include <set>
#include <vector>

/// Tracks the current and final values of symbols during behavioral
/// synthesis (always/initial blocks).
class value_mapt
{
public:
  class mapt
  {
  public:
    typedef std::map<irep_idt, exprt> symbol_mapt;
    symbol_mapt symbol_map;

    std::set<irep_idt> changed;

    void assign(const irep_idt &symbol, const exprt &rhs)
    {
      changed.insert(symbol);
      symbol_map[symbol] = rhs;
    }
  } current, final;

  void clear_changed()
  {
    current.changed.clear();
    final.changed.clear();
  }

  // current guard
  exprt::operandst guard;

  exprt guarded_expr(exprt) const;
};

/// Call frame for task/function inlining.
class tf_framet
{
public:
  std::optional<symbol_exprt> return_value;
  std::vector<value_mapt> return_statement_states;
};

/// State for break/continue during loop unrolling.
class loop_framet
{
public:
  // These are in program order
  std::vector<value_mapt> break_statement_states;
  std::vector<value_mapt> continue_statement_states;
};

/// Groups the mutable state used during behavioral statement synthesis.
class verilog_synthesis_behavioral_statet
{
public:
  enum class constructt
  {
    INITIAL,
    ALWAYS,
    ALWAYS_COMB,
    ALWAYS_FF,
    ALWAYS_LATCH,
    OTHER
  };

  enum class event_guardt
  {
    NONE,
    CLOCK,
    COMBINATIONAL
  };

  constructt construct;
  event_guardt event_guard;

  value_mapt *value_map = nullptr;
  std::optional<tf_framet> tf_frame;
  std::optional<loop_framet> loop_frame;
};

#endif // CPROVER_VERILOG_SYNTHESIS_BEHAVIORAL_H
