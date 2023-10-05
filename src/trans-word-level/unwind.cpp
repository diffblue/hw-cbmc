/*******************************************************************\

Module: Unwinding Transition Systems

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/namespace.h>
#include <util/find_symbols.h>
#include <util/expr_util.h>

#include "instantiate_word_level.h"
#include "unwind.h"

/*******************************************************************\

Function: unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind(const transt &trans, message_handlert &message_handler,
            decision_proceduret &decision_procedure, unsigned no_timeframes,
            const namespacet &ns, bool initial_state) {
  messaget message{message_handler};
  const exprt &op_invar=trans.invar();
  const exprt &op_init=trans.init();
  const exprt &op_trans=trans.trans();

  // in-state constraints

  message.status() << "In-state constraints" << messaget::eom;

  if(!op_invar.is_true())
    for(unsigned c=0; c<no_timeframes; c++)
      decision_procedure.set_to_true(
        instantiate(op_invar, c, no_timeframes, ns));

  // initial state

  if(initial_state)
  {
    message.status() << "Initial state" << messaget::eom;

    if(!op_init.is_true())
      decision_procedure.set_to_true(
        instantiate(op_init, 0, no_timeframes, ns));
  }

  // transition relation

  message.status() << "Transition relation" << messaget::eom;

  if(!op_trans.is_true())
    for(unsigned t=0; t<no_timeframes; t++)
    {
      // do transitions
      bool last=(t==no_timeframes-1);

      if(last)
        message.status() << "Transition " << t << messaget::eom;
      else
        message.status() << "Transition " << t << "->" << t+1 << messaget::eom;
                  
      decision_procedure.set_to_true(
        instantiate(op_trans, t, no_timeframes, ns));
    }
}
