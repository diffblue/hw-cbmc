/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/ebmc_util.h>

#include "verilog_expr.h"
#include "verilog_typecheck.h"

/*******************************************************************\

Function: verilog_typecheckt::verilog_interpreter

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::verilog_interpreter(
  const verilog_statementt &statement)
{
  if(statement.id() == ID_verilog_blocking_assign)
  {
    const verilog_blocking_assignt &assign=
      to_verilog_blocking_assign(statement);

    exprt rhs = elaborate_constant_expression(assign.rhs());
    if(!rhs.is_constant())
    {
      throw errort().with_location(assign.rhs().source_location())
        << "right-hand side of assignment is not constant";
    }

    if(assign.lhs().id()==ID_symbol)
    {
      const irep_idt &identifier = to_symbol_expr(assign.lhs()).identifier();
      vars[identifier]=rhs;

#if 0
      status() << "ASSIGN " << identifier << " <- " << to_string(rhs) << eom;
#endif
    }
  }
  else if(statement.id()==ID_block)
  {
    for(const auto & s : statement.operands())
      verilog_interpreter(to_verilog_statement(s));
  }
  else if(statement.id()==ID_for)
  {
    const verilog_fort &verilog_for=to_verilog_for(statement);

    for(auto &init : verilog_for.initialization())
      verilog_interpreter(init);

    while(true)
    {
      exprt cond = elaborate_constant_expression(verilog_for.condition());

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
          throw errort().with_location(verilog_for.source_location())
            << "for condition is not constant: " << cond.pretty();
        }

        if(cond_i==0) break;
      }

      verilog_interpreter(verilog_for.body());
      verilog_interpreter(verilog_for.inc_statement());
    }
  }
  else if(statement.id() == ID_if)
  {
    const verilog_ift &verilog_if = to_verilog_if(statement);

    exprt cond = elaborate_constant_expression(verilog_if.cond());

    bool taken;

    if(cond.is_true())
      taken = true;
    else if(cond.is_false())
      taken = false;
    else
    {
      mp_integer cond_i;

      if(to_integer_non_constant(cond, cond_i))
      {
        throw errort().with_location(verilog_if.source_location())
          << "if condition is not constant: " << cond.pretty();
      }

      taken = (cond_i != 0);
    }

    if(taken)
      verilog_interpreter(verilog_if.then_case());
    else if(verilog_if.has_else_case())
      verilog_interpreter(verilog_if.else_case());
  }
  else
  {
    throw errort().with_location(statement.source_location())
      << "Don't know how to interpret statement `" << statement.id() << '\'';
  }
}
