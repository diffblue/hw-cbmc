/*******************************************************************\

Module: The set_inputs() statement

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/namespace.h>
#include <util/symbol.h>
#include <util/expr_util.h>
#include <util/arith_tools.h>

#include <ansi-c/c_types.h>

#include "set_inputs.h"

/*******************************************************************\

Function: add_set_inputs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void add_set_inputs(
  symbolt &symbol,
  const irep_idt &struct_identifier,
  const std::set<irep_idt> &top_level_inputs,
  const namespacet &ns)
{
  code_blockt block;

  // the variables we use
  const symbolt &struct_symbol=ns.lookup(struct_identifier);
  const symbolt &array_symbol=ns.lookup(id2string(struct_identifier)+"_array");
  const symbolt &timeframe_symbol=ns.lookup("hw-cbmc::timeframe");
  
  const struct_typet &struct_type=
    to_struct_type(ns.follow(struct_symbol.type));
  
  // We now assume current input values to be equal,
  // with the goal of adding assumptions on inputs.
  exprt index_expr(ID_index, struct_symbol.type);
  index_expr.copy_to_operands(symbol_expr(array_symbol), symbol_expr(timeframe_symbol));

  for(std::set<irep_idt>::const_iterator
      i_it=top_level_inputs.begin();
      i_it!=top_level_inputs.end();
      i_it++)
  {
    struct_typet::componentt component=struct_type.get_component(*i_it);
    assert(component.is_not_nil());
  
    exprt member_expr1=member_exprt(symbol_expr(struct_symbol), *i_it, component.type());
    exprt member_expr2=member_exprt(index_expr, *i_it, component.type());
  
    code_assumet input_assumption(equal_exprt(member_expr1, member_expr2));
    block.move_to_operands(input_assumption);
  }

  // add code to symbol
  symbol.value=block;

  // hide and inline
  symbol.type.set(ID_C_hide, true);
  symbol.type.set(ID_C_inlined, true);
}
