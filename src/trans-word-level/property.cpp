/*******************************************************************\

Module: Unwinding the Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>

#include <util/namespace.h>
#include <util/std_expr.h>

#include "instantiate_word_level.h"
#include "property.h"

/*******************************************************************\

Function: property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void property(
  const exprt &property_expr,
  exprt::operandst &prop_handles,
  message_handlert &message_handler,
  decision_proceduret &solver,
  unsigned no_timeframes,
  const namespacet &ns)
{
  messaget message(message_handler);

  if(property_expr.is_true())
  {
    prop_handles.resize(no_timeframes, true_exprt());
    return;
  }

  if(property_expr.id()!=ID_AG &&
     property_expr.id()!=ID_sva_always)
  {
    message.error() << "unsupported property - only SVA always implemented"
                    << messaget::eom;
    exit(1);
  }

  const exprt &p = to_unary_expr(property_expr).op();

  for(unsigned c=0; c<no_timeframes; c++)
  {
    exprt tmp=
      instantiate(p, c, no_timeframes, ns);

    auto handle = solver.handle(tmp);
    prop_handles.push_back(std::move(handle));
  }
}
