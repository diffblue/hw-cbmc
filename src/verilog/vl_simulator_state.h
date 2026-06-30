/*******************************************************************\

Module: Verilog Simulator State

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_VL_SIMULATOR_STATE_H
#define CPROVER_VERILOG_VL_SIMULATOR_STATE_H

#include <util/irep.h>
#include <util/mp_arith.h>

#include <map>
#include <optional>

class exprt;

class vl_simulator_statet
{
public:
  // Runtime variable state: identifier -> value
  std::map<irep_idt, mp_integer> state;

  // Simulation time
  mp_integer current_time = 0;

  // Set when $finish or $fatal is called
  std::optional<int> finish_code;

  // Set when an assertion fails
  bool assertion_failure = false;

  /// Evaluate an expression to an integer value.
  mp_integer eval_expr(const exprt &);
};

#endif // CPROVER_VERILOG_VL_SIMULATOR_STATE_H
