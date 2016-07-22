/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>

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
  if(statement.id()==ID_blocking_assign)
  {
    const verilog_blocking_assignt &assign=
      to_verilog_blocking_assign(statement);

    exprt rhs=elaborate_const_expression(assign.rhs());
    if(!rhs.is_constant())
    {
      error().source_location=assign.rhs().source_location();
      error() << "right-hand side of assignment is not constant" << eom;
      throw 0;
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
    verilog_interpreter(verilog_for.initialization());
    
    while(true)
    {
      exprt cond=elaborate_const_expression(verilog_for.condition());
      
      mp_integer cond_i;
      if(to_integer(cond, cond_i))
      {
        error().source_location=verilog_for.source_location();
        error() << "for condition is not constant" << eom;
        throw 0;
      }
      
      if(cond_i==0) break;

      verilog_interpreter(verilog_for.body());
      verilog_interpreter(verilog_for.inc_statement());
    }
  }
  else
  {
    error().source_location=statement.source_location();
    error() << "Don't know how to interpret statement `"
            << statement.id() << '\'' << eom;
    throw 0;
  }
}
