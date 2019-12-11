/*******************************************************************\

Module: Unwinding the Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>

#include <util/namespace.h>

#include "instantiate_word_level.h"
#include "property.h"

/*******************************************************************\

Function: property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void property(const exprt &property_expr, bvt &prop_bv,
              message_handlert &message_handler, prop_conv_solvert &solver,
              unsigned no_timeframes, const namespacet &ns) {
  messaget message(message_handler);

  if(property_expr.is_true())
  {
    prop_bv.resize(no_timeframes, const_literal(true));
    return;
  }

  if(property_expr.id()!=ID_AG &&
     property_expr.id()!=ID_sva_always)
  {
    message.error() << "unsupported property - only SVA always implemented"
                    << messaget::eom;
    exit(1);
  }

  assert(property_expr.operands().size()==1);

  const exprt &p=property_expr.op0();
  
  for(unsigned c=0; c<no_timeframes; c++)
  {
    exprt tmp=
      instantiate(p, c, no_timeframes, ns);

    literalt l=solver.convert(tmp);
    prop_bv.push_back(l);
  }
}
