/*******************************************************************\

Module: Predicate Abstraction Auxiliary Code

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <solvers/prop/prop.h>

#include "predabs_aux.h"

/*******************************************************************\

Function: make_pos

  Inputs:

 Outputs:

 Purpose: ensures that the literal is positive
          and that all literals that are quantified over
          are unique

\*******************************************************************/

literalt make_pos(prop_convt &conv, const exprt &expr)
{
   literalt l=conv.convert(expr);
   literalt tmp=conv.prop.new_variable();
   conv.prop.set_equal(tmp, l);
   assert(!tmp.sign());
   return tmp;
}

/*******************************************************************\

Function: uses_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool uses_symbol(const exprt &expr,
                 const std::set<irep_idt> &symbols)
 {
  forall_operands(it, expr)
    if(uses_symbol(*it, symbols))
      return true;

  if(expr.id()==ID_symbol)
    return symbols.find(expr.get(ID_identifier))!=symbols.end();

  return false;
 }
