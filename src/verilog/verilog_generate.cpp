/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_typecheck.h"

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_block(
  const exprt &statement,
  exprt::operandst &dest)
{
  forall_operands(it, statement)
    elaborate_generate_item(*it, dest);
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_item

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_item(
  const exprt &statement,
  exprt::operandst &dest)
{
  if(statement.id()=="generate_block")
    elaborate_generate_block(statement, dest);
  else if(statement.id()=="generate_case")
    elaborate_generate_case(statement, dest);
  else if(statement.id()=="generate_if")
    elaborate_generate_if(statement, dest);
  else if(statement.id()=="generate_for")
    elaborate_generate_for(statement, dest);
  else if(statement.id()=="decl" &&
          statement.get("class")=="genvar")
  {
    forall_operands(it, statement)
      genvars[it->get("identifier")]=-1;
  }
  else
  {
    // no need for elaboration
    exprt tmp("set_genvars");
    tmp.copy_to_operands(statement);
    irept &variables=tmp.add("variables");
    
    for(genvarst::const_iterator it=genvars.begin();
        it!=genvars.end();
        it++)
      variables.set(it->first, integer2string(it->second));

    dest.push_back(exprt());
    dest.back().swap(tmp);
  }
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_case

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_case(
  const exprt &statement,
  exprt::operandst &dest)
{
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_if(
  const exprt &statement,
  exprt::operandst &dest)
{
  if(statement.operands().size()!=3 &&
     statement.operands().size()!=2)
  {
    err_location(statement);
    throw "generate_for expects two or three operands";
  }
  
  mp_integer condition;
  convert_const_expression(statement.op0(), condition);

  if(condition==0)
  {
    if(statement.operands().size()==3)
      elaborate_generate_item(statement.op2(), dest);
  }
  else
    elaborate_generate_item(statement.op1(), dest);
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_assign(
  const exprt &statement,
  exprt::operandst &dest)
{
  if(statement.operands().size()!=2)
  {
    err_location(statement);
    throw "generate_assign expects two operands";
  }
  
  if(statement.op0().id()!="symbol")
  {
    err_location(statement.op0());
    str << "expected symbol on left hand side of assignment";
    throw 0;
  }
  
  const irep_idt &identifier=statement.op0().get("identifier");
  
  genvarst::iterator it=genvars.find(identifier);
  
  if(it==genvars.end())
  {
    err_location(statement.op0());
    str << "expected genvar on left hand side of assignment";
    throw 0;
  }
  
  mp_integer rhs;
  
  convert_const_expression(statement.op1(), rhs);
  
  if(rhs<0)
  {
    err_location(statement.op1());
    str << "must not assign negative value to genvar";
    throw 0;
  }
  
  it->second=rhs;
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_for

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_for(
  const exprt &statement,
  exprt::operandst &dest)
{
  if(statement.operands().size()!=4)
  {
    err_location(statement);
    throw "generate_for expects four operands";
  }
  
  elaborate_generate_assign(statement.op0(), dest);

  while(true)
  {
    mp_integer condition;
    convert_const_expression(statement.op1(), condition);
  
    if(condition==0) break;
    
    // order is important!
    elaborate_generate_item(statement.op3(), dest);
    elaborate_generate_assign(statement.op2(), dest);
  }
}
