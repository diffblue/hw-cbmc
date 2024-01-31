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
    if(item.id() == ID_generate_block)
      elaborate_generate_item(item, dest);
    else if(
      item.id() == ID_decl &&
      to_verilog_decl(item).get_class() == ID_verilog_genvar)
    {
      // Assign to "-1", which signals "the variable is unset"
      for(auto &declarator : to_verilog_decl(item).declarators())
        genvars[declarator.identifier()] = -1;
    }
    else
      dest.push_back(item); // copy

  return verilog_module_expr;
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_block(
  const verilog_generate_blockt &generate_block,
  module_itemst &dest)
{
  // These introduce a scope, and generate-for may append a
  // loop index to the label. We hence leave a generate_block
  // module item.
  bool is_named = generate_block.is_named();

  if(is_named)
    enter_named_block(generate_block.base_name());

  module_itemst new_module_items;

  for(auto &item : generate_block.module_items())
    elaborate_generate_item(item, new_module_items);

  auto identifier = generate_block.base_name();
  auto block = verilog_generate_blockt(identifier, std::move(new_module_items));
  block.add_source_location() = generate_block.source_location();

  dest.push_back(std::move(block));

  if(is_named)
    named_blocks.pop_back();
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

  if(decl_class == ID_verilog_genvar)
  {
    // Assign to "-1", which signals "the variable is unset"
    for(auto &declarator : decl.declarators())
      genvars[declarator.identifier()] = -1;
  }
  else
  {
    if(decl_class == ID_reg || decl_class == ID_wire)
    {
      // verilog_typecheckt::module_interfaces does not add
      // symbols in generate blocks, since the generate blocks
      // have not yet been elaborated. Do so now.
      interface_module_decl(decl);
    }

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

Function: verilog_typecheckt::elaborate_generate_inst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_inst(
  const verilog_instt &inst,
  module_itemst &dest)
{
  // verilog_typecheckt::module_interfaces does not add
  // symbols for module instances in generate blocks,
  // since the generate blocks have not yet been elaborated.
  // Do so now.
  interface_inst(inst);

  // Preserve the instantiation
  verilog_set_genvarst tmp(inst);
  auto &variables = tmp.variables();

  for(const auto &it : genvars)
    variables[it.first] = irept(integer2string(it.second));

  dest.push_back(std::move(tmp));
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
    elaborate_generate_block(to_verilog_generate_block(statement), dest);
  else if(statement.id()==ID_generate_case)
    elaborate_generate_case(to_verilog_generate_case(statement), dest);
  else if(statement.id()==ID_generate_if)
    elaborate_generate_if(to_verilog_generate_if(statement), dest);
  else if(statement.id()==ID_generate_for)
    elaborate_generate_for(to_verilog_generate_for(statement), dest);
  else if(statement.id() == ID_decl)
    elaborate_generate_decl(to_verilog_decl(statement), dest);
  else if(statement.id() == ID_inst)
    elaborate_generate_inst(to_verilog_inst(statement), dest);
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
  const verilog_generate_caset &statement,
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
  const verilog_generate_ift &statement,
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
  const verilog_generate_assignt &statement,
  module_itemst &dest)
{
  if(statement.lhs().id() != ID_symbol)
  {
    error().source_location = statement.lhs().source_location();
    error() << "expected symbol on left hand side of assignment" << eom;
    throw 0;
  }

  const irep_idt &identifier = to_symbol_expr(statement.lhs()).get_identifier();

  genvarst::iterator it=genvars.find(identifier);
  
  if(it==genvars.end())
  {
    error().source_location = statement.lhs().source_location();
    error() << "expected genvar on left hand side of assignment" << eom;
    throw 0;
  }

  mp_integer rhs = convert_integer_constant_expression(statement.rhs());

  if(rhs<0)
  {
    error().source_location = statement.rhs().source_location();
    error() << "must not assign negative value to genvar" << eom;
    throw 0;
  }
  
  it->second=rhs;
}

/*******************************************************************\

Function: verilog_typecheckt::generate_for_loop_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheckt::generate_for_loop_index(
  const exprt &initialization_statement) const
{
  if(initialization_statement.id() == ID_generate_assign)
  {
    auto &assignment = to_binary_expr(initialization_statement);
    return assignment.lhs();
  }
  else
  {
    error().source_location = initialization_statement.source_location();
    error() << "failed to determine generate loop index" << eom;
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_for

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_for(
  const verilog_generate_fort &for_statement,
  module_itemst &dest)
{
  elaborate_generate_assign(for_statement.init(), dest);

  // work out what the loop index is
  auto loop_index = generate_for_loop_index(for_statement.init());

  while(true)
  {
    mp_integer condition =
      convert_integer_constant_expression(for_statement.cond());

    if(condition==0) break;

    // Order is important!
    // First execute the block.
    // If it's a generate_block, append the loop counter to
    // the block's identifier, surrounded by square brackets.
    auto copy_of_body = for_statement.body();
    if(copy_of_body.id() == ID_generate_block)
    {
      auto &generate_block = to_verilog_generate_block(copy_of_body);
      const mp_integer loop_index_int =
        convert_integer_constant_expression(loop_index);
      auto new_base_name = id2string(generate_block.base_name()) + '[' +
                           integer2string(loop_index_int) + ']';
      generate_block.base_name(new_base_name);
    }

    elaborate_generate_item(copy_of_body, dest);

    // Now increase the loop counter.
    elaborate_generate_assign(for_statement.increment(), dest);
  }
}
