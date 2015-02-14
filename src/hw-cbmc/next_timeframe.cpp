/*******************************************************************\

Module: The next_timeframe() statement

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/namespace.h>
#include <util/symbol.h>
#include <util/expr_util.h>
#include <util/arith_tools.h>

#include <ansi-c/c_types.h>

#include "next_timeframe.h"

/*******************************************************************\

Function: add_next_timeframe

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void add_next_timeframe(
  symbolt &symbol,
  const irep_idt &struct_identifier,
  const std::set<irep_idt> &top_level_inputs,
  const namespacet &ns)
{
  // the variables we use
  const symbolt &struct_symbol=ns.lookup(struct_identifier);
  const symbolt &array_symbol=ns.lookup(id2string(struct_identifier)+"_array");
  const symbolt &timeframe_symbol=ns.lookup("hw-cbmc::timeframe");
  
  // we first increase the tick
  symbol_exprt timeframe_expr=symbol_expr(timeframe_symbol);
  
  const plus_exprt plus_expr(
    timeframe_expr, from_integer(1, index_type()), index_type());
  
  const code_assignt assignment_increase(timeframe_expr, plus_expr);
  
  code_blockt block;
  block.add(assignment_increase);

  // now assign the non-inputs in the module symbol
  const index_exprt index_expr(
    symbol_expr(array_symbol),
    symbol_expr(timeframe_symbol),
    struct_symbol.type);

  const struct_typet &struct_type=
    to_struct_type(ns.follow(struct_symbol.type));
    
  const struct_typet::componentst &components=
    struct_type.components();

  for(struct_typet::componentst::const_iterator
      c_it=components.begin();
      c_it!=components.end();
      c_it++)
  {
    if(c_it->get_is_padding()) continue;
    irep_idt name=c_it->get_name();
    const typet &type=c_it->type();
    
    if(top_level_inputs.find(name)!=top_level_inputs.end()) continue;
  
    const exprt member_expr1=member_exprt(symbol_expr(struct_symbol), name, type);
    const exprt member_expr2=member_exprt(index_expr, name, type);
  
    const code_assignt member_assignment(member_expr1, member_expr2);
    block.add(member_assignment);
  }

  // add code to symbol
  symbol.value=block;

  // hide and inline
  symbol.type.set(ID_C_hide, true);
  symbol.type.set(ID_C_inlined, true);
}
