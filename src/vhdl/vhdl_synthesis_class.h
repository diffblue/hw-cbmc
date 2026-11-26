/*******************************************************************\

Module: VHDL Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VHDL_VHDL_SYNTHESIS_CLASS_H
#define CPROVER_VHDL_VHDL_SYNTHESIS_CLASS_H

#include <util/message.h>
#include <util/namespace.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include "vhdl_expr.h"

#include <map>
#include <optional>
#include <set>

/// Turns the type-checked architecture into a transition system.
///
/// There is one implicit clock. A process that contains a clock edge
/// condition (clk'event and clk='1', rising_edge(clk)) is a clocked
/// process; its body is executed once per clock cycle, with the edge
/// condition taken to be true, and the signals and variables it
/// assigns are state variables with next-state functions (TRANS).
/// Any other process, and the concurrent signal assignments, are
/// combinational; the signals they assign are constrained in every
/// state (INVAR). Initial values of objects are INIT constraints.
/// Assertions are properties.
class vhdl_synthesist
{
public:
  vhdl_synthesist(
    symbol_table_baset &_symbol_table,
    irep_idt _module,
    message_handlert &_message_handler)
    : symbol_table(_symbol_table),
      ns(_symbol_table),
      module(_module),
      message(_message_handler)
  {
  }

  bool operator()();

protected:
  symbol_table_baset &symbol_table;
  const namespacet ns;
  const irep_idt module;
  messaget message;
  const symbolt *module_symbol = nullptr;

  unsigned property_counter = 0;

  exprt::operandst trans, init, invar;

  /// the objects that are assigned, and the statement that assigns
  /// them (IEEE 1076-2008 6.4.2.3: a signal has one driver per process)
  std::map<irep_idt, unsigned> drivers;
  unsigned current_driver = 0;

  /// the signals with a combinational driver
  std::set<irep_idt> combinational_signals;

  /// the clock signal and edge polarity; there is one clock
  struct clockt
  {
    irep_idt signal;
    bool rising;
  };
  std::optional<clockt> clock;

  /// the values of the objects during the symbolic execution
  /// of a statement; the key is the symbol identifier
  using valuest = std::map<irep_idt, exprt>;

  void synth_module(const irept &);
  void synth_process(const vhdl_processt &);
  /// synthesise a process body or a concurrent statement
  void synth_statement(const codet &, bool clocked);
  void synth_property(
    const exprt &condition,
    irep_idt label,
    const exprt &report,
    const source_locationt &);

  /// symbolic execution of a statement
  void execute(const codet &, const exprt &guard, valuest &, bool clocked);

  void execute_assign(
    const vhdl_code_assignt &,
    const exprt &guard,
    valuest &,
    bool clocked);

  /// replace the variables by their current values
  exprt substitute(exprt, const valuest &) const;

  /// the value of an object: the value in the map, or the symbol
  exprt value_of(const symbol_exprt &, const valuest &) const;

  /// the current value of (part of) an object, given as
  /// assignment target
  exprt current_value(exprt target, const valuest &) const;

  /// replace the variables in the indices of an assignment target
  exprt substitute_indices(exprt target, const valuest &) const;

  /// the new value of an object after assigning to (part of) it
  static exprt with_type(exprt, const typet &);
  exprt assign_to(const exprt &lhs, exprt rhs, const valuest &) const;

  /// Is this a clock edge condition? If so, the clock is recorded,
  /// and an error is raised if it differs from an earlier clock.
  bool is_clock_edge(const exprt &);

  /// does the expression contain a clock edge?
  static bool contains_clock_edge(const exprt &);

  /// check that no clock edge remains in the transition system
  void check_no_clock_edge(const exprt &) const;

  /// is this the body of a clocked process? Rejects unsupported uses
  /// of clock edges.
  bool is_clocked_process(const code_blockt &body) const;

  const symbolt &lookup(const symbol_exprt &) const;
};

#endif // CPROVER_VHDL_VHDL_SYNTHESIS_CLASS_H
