/*******************************************************************\

Module: Verilog Simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_SIMULATOR_H
#define CPROVER_VERILOG_SIMULATOR_H

#include <util/expr.h>
#include <util/namespace.h>

#include <map>

class verilog_statementt;
class verilog_typecheck_exprt;

/// A Verilog simulator, used during elaboration to evaluate constant
/// expressions and constant function calls
/// (Section 11.2.1 IEEE 1800-2017). It maintains the simulator state
/// (a valuation of the variables), evaluates expressions over that
/// state, and executes statements that do not progress simulation
/// time.
class verilog_simulatort
{
public:
  verilog_simulatort(
    verilog_typecheck_exprt &_typecheck_expr,
    const namespacet &_ns)
    : typecheck_expr(_typecheck_expr), ns(_ns)
  {
  }

  // The simulator state, a valuation of the variables.
  using varst = std::map<irep_idt, exprt>;
  varst vars;

  /// the value of the given variable, or nil if there is none
  exprt var_value(const irep_idt &identifier) const;

  /// Evaluate the given expression over the simulator state.
  /// Expressions that cannot be evaluated are returned unchanged.
  exprt evaluate_expr(exprt);

  /// Execute a statement that does not progress simulation time.
  void execute(const verilog_statementt &);

protected:
  // hooks into elaboration and type checking
  verilog_typecheck_exprt &typecheck_expr;

  const namespacet &ns;

  exprt evaluate_expr_rec(exprt);
};

#endif
