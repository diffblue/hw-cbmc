/*******************************************************************\

Module: Verilog Simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VLSIM_VL_SIMULATOR_H
#define CPROVER_VLSIM_VL_SIMULATOR_H

#include <util/message.h>
#include <util/mp_arith.h>
#include <util/symbol_table.h>

#include <map>
#include <optional>
#include <string>

class exprt;
class verilog_statementt;
class verilog_module_exprt;

class vl_simulatort : public messaget
{
public:
  vl_simulatort(
    const symbol_tablet &_symbol_table,
    message_handlert &_message_handler)
    : messaget(_message_handler), symbol_table(_symbol_table)
  {
  }

  /// Run the simulation for the given top-level module.
  /// Returns the exit code: 0 for success, non-zero for failure.
  int simulate(const irep_idt &module_symbol);

  /// Evaluate an expression to an integer value.
  mp_integer eval_expr(const exprt &);

private:
  const symbol_tablet &symbol_table;

  // Runtime variable state: identifier -> value
  std::map<irep_idt, mp_integer> state;

  // Simulation time
  mp_integer current_time = 0;

  // Set when $finish or $fatal is called
  std::optional<int> finish_code;

  // Set when an assertion fails
  bool assertion_failure = false;

  void run_module(const verilog_module_exprt &);
  void run_statement(const verilog_statementt &);
  void run_system_task(const std::string &name, const exprt::operandst &args);
  std::string format_display(
    const std::string &fmt,
    const exprt::operandst &args,
    std::size_t &arg_index);
};

#endif // CPROVER_VLSIM_VL_SIMULATOR_H
