/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>

#include "verilog_expr.h"
#include "verilog_typecheck.h"

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

Function: verilog_typecheckt::elaborate_generate_item

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

verilog_typecheckt::module_itemst verilog_typecheckt::elaborate_generate_item(
  const verilog_module_itemt &module_item)
{
  module_itemst dest;

  if(module_item.id() == ID_generate_block)
    elaborate_generate_block(to_verilog_generate_block(module_item), dest);
  else if(module_item.id() == ID_generate_case)
    elaborate_generate_case(to_verilog_generate_case(module_item), dest);
  else if(module_item.id() == ID_generate_if)
    elaborate_generate_if(to_verilog_generate_if(module_item), dest);
  else if(module_item.id() == ID_generate_for)
    elaborate_generate_for(to_verilog_generate_for(module_item), dest);
  else
  {
    // E.g., declarations. Remember the values of the
    // generate variables.
    verilog_set_genvarst set_genvars(module_item);
    irept &variables = set_genvars.add("variables");

    for(const auto &it : genvars)
      variables.set(it.first, integer2string(it.second));

    dest = elaborate_level({set_genvars});
  }

  return dest;
}

void verilog_typecheckt::elaborate_generate_item(
  const verilog_module_itemt &module_item,
  module_itemst &dest)
{
  auto result = elaborate_generate_item(module_item);
  dest.insert(dest.end(), result.begin(), result.end());
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
    throw errort().with_location(statement.source_location())
      << "generate_if expects two or three operands";
  }

  mp_integer condition =
    convert_integer_constant_expression(to_multi_ary_expr(statement).op0());

  if(condition==0)
  {
    if(statement.operands().size()==3)
      elaborate_generate_item(
        to_verilog_module_item(to_multi_ary_expr(statement).op2()), dest);
  }
  else
    elaborate_generate_item(
      to_verilog_module_item(to_multi_ary_expr(statement).op1()), dest);
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
  if(statement.lhs().id() != ID_verilog_identifier)
  {
    throw errort().with_location(statement.lhs().source_location())
      << "expected symbol on left hand side of assignment";
  }

  const irep_idt &identifier =
    to_verilog_identifier_expr(statement.lhs()).base_name();

  genvarst::iterator it=genvars.find(identifier);
  
  if(it==genvars.end())
  {
    throw errort().with_location(statement.lhs().source_location())
      << "expected genvar on left hand side of assignment";
  }

  mp_integer rhs = convert_integer_constant_expression(statement.rhs());

  if(rhs<0)
  {
    throw errort().with_location(statement.rhs().source_location())
      << "must not assign negative value to genvar";
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
    throw errort().with_location(initialization_statement.source_location())
      << "failed to determine generate loop index";
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

    // Now increase/decrease the loop counter.
    {
      auto statement = for_statement.iteration().id();
      if(statement == ID_generate_assign)
      {
        elaborate_generate_assign(
          to_verilog_generate_assign(for_statement.iteration()), dest);
      }
      else if(statement == ID_preincrement || statement == ID_predecrement)
      {
        // turn ++x and x++ into x = x + 1
        // turn --x and x-- into x = x - 1
        // The expressions are parse trees, prior to typechecking
        auto &op = to_unary_expr(for_statement.iteration()).op();
        auto one = constant_exprt{ID_1, typet{}};
        auto new_value = binary_exprt{
          op, statement == ID_preincrement ? ID_plus : ID_minus, one, typet{}};
        auto assignment = verilog_generate_assignt{op, new_value};

        elaborate_generate_assign(assignment, dest);
      }
      else
      {
        DATA_INVARIANT_WITH_DIAGNOSTICS(
          false,
          "unexpected genvar_iteration item",
          for_statement.iteration().pretty());
      }
    }
  }
}
