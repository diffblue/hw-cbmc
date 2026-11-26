/*******************************************************************\

Module: Unwinding Transition Systems

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "unwind.h"

#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/namespace.h>

#include <solvers/decision_procedure.h>

#include "instantiate_word_level.h"

/*******************************************************************\

Function: unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind(
  const transt &trans,
  message_handlert &message_handler,
  decision_proceduret &decision_procedure,
  std::size_t from_timeframe,
  std::size_t to_timeframe,
  const namespacet &ns,
  word_level_unwind_optionst options)
{
  PRECONDITION(from_timeframe <= to_timeframe);

  messaget message{message_handler};
  const exprt &op_invar=trans.invar();
  const exprt &op_init=trans.init();
  const exprt &op_trans=trans.trans();

  // instantiate(...) does not depend on the total number of
  // timeframes; we pass to_timeframe.
  const std::size_t no_timeframes = to_timeframe;

  // in-state constraints

  if(options.add_constraints)
  {
    message.progress() << "In-state constraints" << messaget::eom;

    if(!op_invar.is_true())
      for(std::size_t c = from_timeframe; c < to_timeframe; c++)
        decision_procedure.set_to_true(instantiate(op_invar, c, no_timeframes));
  }

  // initial state

  if(options.add_initial_state && from_timeframe == 0)
  {
    message.progress() << "Initial state" << messaget::eom;

    if(!op_init.is_true())
      decision_procedure.set_to_true(instantiate(op_init, 0, no_timeframes));
  }

  // transition relation

  message.progress() << "Transition relation" << messaget::eom;

  if(!op_trans.is_true())
    for(std::size_t t = from_timeframe; t < to_timeframe; t++)
    {
      // do transitions
      bool last = (t == to_timeframe - 1);

      if(last)
        message.progress() << "Transition " << t << messaget::eom;
      else
        message.progress() << "Transition " << t << "->" << t + 1
                           << messaget::eom;

      decision_procedure.set_to_true(instantiate(op_trans, t, no_timeframes));
    }
}

/*******************************************************************\

Function: unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind(
  const transt &trans,
  message_handlert &message_handler,
  decision_proceduret &decision_procedure,
  std::size_t no_timeframes,
  const namespacet &ns,
  word_level_unwind_optionst options)
{
  unwind(
    trans, message_handler, decision_procedure, 0, no_timeframes, ns, options);
}
