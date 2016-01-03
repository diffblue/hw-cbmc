/*******************************************************************\

Module: Unwinding the Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/namespace.h>
#include <util/cout_message.h>

#include "instantiate_netlist.h"
#include "property_netlist.h"

/*******************************************************************\

Function: property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void property(
  const exprt &property_expr,
  bvt &prop_bv,
  message_handlert &message_handler,
  propt &solver,
  const bmc_mapt &map,
  const namespacet &ns)
{
  if(property_expr.is_true())
  {
    prop_bv.resize(map.get_no_timeframes(), const_literal(true));
    return;
  }
  
  if(property_expr.id()!=ID_AG &&
     property_expr.id()!=ID_sva_always)
    throw "unsupported property - only SVA always implemented";
  
  assert(property_expr.operands().size()==1);

  const exprt &p=property_expr.op0();
  
  for(unsigned c=0; c<map.get_no_timeframes(); c++)
  {
    literalt l=instantiate_convert(solver, map, p, c, c+1, ns, message_handler);
    prop_bv.push_back(l);
  }
}

