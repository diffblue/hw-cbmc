/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_typecheck.h"

#include "verilog_expr.h"

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_block(
  const exprt &statement,
  module_itemst &dest)
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
  module_itemst &dest)
{
  if(statement.id()==ID_generate_block)
    elaborate_generate_block(statement, dest);
  else if(statement.id()==ID_generate_case)
    elaborate_generate_case(statement, dest);
  else if(statement.id()==ID_generate_if)
    elaborate_generate_if(statement, dest);
  else if(statement.id()==ID_generate_for)
    elaborate_generate_for(statement, dest);
  else if(statement.id()==ID_decl &&
          statement.get(ID_class)==ID_genvar)
  {
    forall_operands(it, statement)
      genvars[it->get(ID_identifier)]=-1;
  }
  else
  {
    // no need for elaboration
    verilog_module_itemt tmp(ID_set_genvars);
    tmp.add_to_operands(statement);
    irept &variables=tmp.add("variables");
    
    for(const auto & it : genvars)
      variables.set(it.first, integer2string(it.second));

    dest.push_back(std::move(tmp));
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
  module_itemst &dest)
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
  module_itemst &dest)
{
  if(statement.operands().size()!=3 &&
     statement.operands().size()!=2)
  {
    error().source_location = statement.source_location();
    error() << "generate_if expects two or three operands" << eom;
    throw 0;
  }

  mp_integer condition =
    convert_const_expression(to_multi_ary_expr(statement).op0());

  if(condition==0)
  {
    if(statement.operands().size()==3)
      elaborate_generate_item(to_multi_ary_expr(statement).op2(), dest);
  }
  else
    elaborate_generate_item(to_multi_ary_expr(statement).op1(), dest);
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_assign(
  const exprt &statement,
  module_itemst &dest)
{
  if(statement.operands().size()!=2)
  {
    error().source_location = statement.source_location();
    error() << "generate_assign expects two operands" << eom;
    throw 0;
  }

  if(to_binary_expr(statement).lhs().id() != ID_symbol)
  {
    error().source_location = to_binary_expr(statement).lhs().source_location();
    error() << "expected symbol on left hand side of assignment" << eom;
    throw 0;
  }

  const irep_idt &identifier =
    to_symbol_expr(to_binary_expr(statement).lhs()).get_identifier();

  genvarst::iterator it=genvars.find(identifier);
  
  if(it==genvars.end())
  {
    error().source_location = to_binary_expr(statement).lhs().source_location();
    error() << "expected genvar on left hand side of assignment" << eom;
    throw 0;
  }

  mp_integer rhs = convert_const_expression(to_binary_expr(statement).rhs());

  if(rhs<0)
  {
    error().source_location = to_binary_expr(statement).rhs().source_location();
    error() << "must not assign negative value to genvar" << eom;
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
  module_itemst &dest)
{
  if(statement.operands().size()!=4)
  {
    error().source_location = statement.source_location();
    error() << "generate_for expects four operands" << eom;
    throw 0;
  }

  elaborate_generate_assign(to_multi_ary_expr(statement).op0(), dest);

  while(true)
  {
    mp_integer condition =
      convert_const_expression(to_multi_ary_expr(statement).op1());

    if(condition==0) break;
    
    // order is important!
    elaborate_generate_item(to_multi_ary_expr(statement).op3(), dest);
    elaborate_generate_assign(to_multi_ary_expr(statement).op2(), dest);
  }
}
