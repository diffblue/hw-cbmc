/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_typecheck.h"

#include "verilog_expr.h"

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_constructs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

verilog_module_exprt verilog_typecheckt::elaborate_generate_constructs(
  const verilog_module_sourcet &module_source)
{
  const auto &module_items = module_source.module_items();

  // We copy the module items to a new verilog_module_exprt
  verilog_module_exprt verilog_module_expr;
  auto &dest = verilog_module_expr.module_items();
  dest.reserve(module_items.size());

  // do the generate stuff, copying the module items
  for(auto &item : module_items)
    elaborate_generate_item(item, dest);

  return verilog_module_expr;
}

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

Function: verilog_typecheckt::elaborate_generate_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_decl(
  const verilog_declt &decl,
  module_itemst &dest)
{
  auto decl_class = decl.get_class();

  if(decl_class == ID_genvar)
  {
    // Assign to "-1", which signals "the variable is unset"
    for(auto &declarator : decl.declarators())
      genvars[declarator.identifier()] = -1;
  }
  else
  {
    // Preserve the declaration for any initializers.
    verilog_module_itemt tmp(ID_set_genvars);
    tmp.add_to_operands(decl);
    irept &variables = tmp.add("variables");

    for(const auto &it : genvars)
      variables.set(it.first, integer2string(it.second));

    dest.push_back(std::move(tmp));
  }
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
  else if(statement.id() == ID_decl)
    elaborate_generate_decl(to_verilog_decl(statement), dest);
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
    convert_integer_constant_expression(to_multi_ary_expr(statement).op0());

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

  mp_integer rhs =
    convert_integer_constant_expression(to_binary_expr(statement).rhs());

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
      convert_integer_constant_expression(to_multi_ary_expr(statement).op1());

    if(condition==0) break;
    
    // order is important!
    elaborate_generate_item(to_multi_ary_expr(statement).op3(), dest);
    elaborate_generate_assign(to_multi_ary_expr(statement).op2(), dest);
  }
}
