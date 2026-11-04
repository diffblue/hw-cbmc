/*******************************************************************\

Module: Verilog Simulator

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VLSIM_VL_SIMULATOR_H
#define CPROVER_VLSIM_VL_SIMULATOR_H

#include <util/message.h>
#include <util/symbol_table.h>

#include <verilog/vl_simulator_state.h>

#include <string>

class verilog_statementt;
class verilog_module_exprt;

class vl_simulatort
{
public:
  vl_simulatort(
    const symbol_tablet &_symbol_table,
    message_handlert &_message_handler)
    : log(_message_handler), symbol_table(_symbol_table)
  {
  }

  /// Run the simulation for the given top-level module.
  /// Returns the exit code: 0 for success, non-zero for failure.
  int simulate(const irep_idt &module_symbol);

private:
  messaget log;
  const symbol_tablet &symbol_table;
  vl_simulator_statet sim_state;

  void run_module(const verilog_module_exprt &);
  void run_statement(const verilog_statementt &);
  void run_system_task(const std::string &name, const exprt::operandst &args);
  std::string format_display(
    const std::string &fmt,
    const exprt::operandst &args,
    std::size_t &arg_index);
};

#endif // CPROVER_VLSIM_VL_SIMULATOR_H
