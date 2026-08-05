/*******************************************************************\

Module: Verilog Simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_simulator.h"

#include <util/ebmc_util.h>
#include <util/mathematical_expr.h>
#include <util/prefix.h>
#include <util/typecheck.h>

#include "verilog_expr.h"
#include "verilog_lowering.h"
#include "verilog_simplifier.h"
#include "verilog_typecheck_expr.h"

/*******************************************************************\

Function: verilog_simulatort::var_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_simulatort::var_value(const irep_idt &identifier) const
{
  varst::const_iterator it = vars.find(identifier);
  if(it == vars.end())
    return nil_exprt();
  else
    return it->second;
}

/*******************************************************************\

Function: verilog_simulatort::evaluate_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_simulatort::evaluate_expr(exprt expr)
{
  // This performs constant-folding on a type-checked expression
  // according to Section 11.2.1 IEEE 1800-2017.
  auto expr_lowered = verilog_lowering(std::move(expr));

  // replace constant symbols
  auto expr_replaced = evaluate_expr_rec(std::move(expr_lowered));

  // finally simplify
  auto expr_simplified = verilog_simplifier(std::move(expr_replaced), ns);

  return expr_simplified;
}

/*******************************************************************\

Function: verilog_simulatort::evaluate_expr_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_simulatort::evaluate_expr_rec(exprt expr)
{
  if(expr.id() == ID_constant)
    return expr;
  else if(expr.id() == ID_symbol)
  {
    const irep_idt &identifier = to_symbol_expr(expr).identifier();

    if(has_prefix(id2string(identifier), "$"))
    {
      // System function identifier. Leave as is.
      return expr;
    }

    auto &symbol = ns.lookup(to_symbol_expr(expr));

    if(symbol.is_macro)
    {
      // Elaborate recursively
      typecheck_expr.elaborate_symbol_rec(symbol.name);

      // A parameter or local parameter. Replace by its value.
      return symbol.value;
    }

    exprt value = var_value(identifier);

#if 0
    status() << "READ " << identifier << " = " << to_string(value) << eom;
#endif

    if(value.is_not_nil())
    {
      source_locationt source_location = expr.source_location();
      exprt tmp = value;
      tmp.add_source_location() = source_location;
      return tmp;
    }
    else
      return expr;
  }
  else if(expr.id() == ID_function_call)
  {
    // Note that the operands are not elaborated yet.
    const function_call_exprt &function_call = to_function_call_expr(expr);

    // Is it a system function call?
    if(function_call.is_system_function_call())
    {
      // These are 'built in'.
      return typecheck_expr.elaborate_constant_system_function_call(
        function_call);
    }
    else
    {
      // Interpret the function.
      return typecheck_expr.elaborate_constant_function_call(function_call);
    }
  }
  else
  {
    // Do any operands first.
    for(auto &op : expr.operands())
    {
      // recursive call
      op = evaluate_expr_rec(op);
    }
    return expr;
  }
}

/*******************************************************************\

Function: verilog_simulatort::execute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_simulatort::execute(const verilog_statementt &statement)
{
  if(statement.id() == ID_verilog_blocking_assign)
  {
    const verilog_blocking_assignt &assign =
      to_verilog_blocking_assign(statement);

    exprt rhs = evaluate_expr(assign.rhs());
    if(!rhs.is_constant())
    {
      throw typecheckt::errort().with_location(assign.rhs().source_location())
        << "right-hand side of assignment is not constant";
    }

    if(assign.lhs().id() == ID_symbol)
    {
      const irep_idt &identifier = to_symbol_expr(assign.lhs()).identifier();
      vars[identifier] = rhs;

#if 0
      status() << "ASSIGN " << identifier << " <- " << to_string(rhs) << eom;
#endif
    }
  }
  else if(statement.id() == ID_block)
  {
    for(const auto &s : statement.operands())
      execute(to_verilog_statement(s));
  }
  else if(statement.id() == ID_for)
  {
    const verilog_fort &verilog_for = to_verilog_for(statement);

    for(auto &init : verilog_for.initialization())
      execute(init);

    while(true)
    {
      exprt cond = evaluate_expr(verilog_for.condition());

      if(cond.is_false())
        break;
      else if(cond.is_true())
      {
      }
      else
      {
        mp_integer cond_i;

        if(to_integer_non_constant(cond, cond_i))
        {
          throw typecheckt::errort().with_location(
            verilog_for.source_location())
            << "for condition is not constant: " << cond.pretty();
        }

        if(cond_i == 0)
          break;
      }

      execute(verilog_for.body());
      execute(verilog_for.inc_statement());
    }
  }
  else
  {
    throw typecheckt::errort().with_location(statement.source_location())
      << "Don't know how to interpret statement `" << statement.id() << '\'';
  }
}
