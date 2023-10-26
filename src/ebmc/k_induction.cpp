/*******************************************************************\

Module: k Induction

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#include "k_induction.h"

#include <trans-word-level/instantiate_word_level.h>
#include <trans-word-level/property.h>
#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/unwind.h>

#include "ebmc_base.h"
#include "ebmc_solver_factory.h"
#include "report_results.h"

/*******************************************************************\

   Class: k_inductiont

 Purpose:

\*******************************************************************/

class k_inductiont:public ebmc_baset
{
public:
  k_inductiont(
    const cmdlinet &_cmdline,
    ui_message_handlert &_ui_message_handler)
    : ebmc_baset(_cmdline, _ui_message_handler),
      ns{transition_system.symbol_table},
      solver_factory(ebmc_solver_factory(_cmdline))
  {
  }

  int operator()();

protected:
  namespacet ns;
  ebmc_solver_factoryt solver_factory;

  int induction_base();
  int induction_step();
};

/*******************************************************************\

Function: do_k_induction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int do_k_induction(
  const cmdlinet &cmdline,
  ui_message_handlert &ui_message_handler)
{
  return k_inductiont(cmdline, ui_message_handler)();
}

/*******************************************************************\

Function: k_inductiont::do_k_induction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int k_inductiont::operator()()
{
  if(get_bound()) return 1;

  int result = get_transition_system(
    cmdline, message.get_message_handler(), transition_system);
  if(result!=-1) return result;

  result = get_properties();
  if(result != -1)
    return result;

  if(properties.properties.empty())
  {
    message.error() << "no properties" << messaget::eom;
    return 1;
  }

  // do induction base
  result=induction_base();
  if(result!=-1) return result;

  // do induction step
  result=induction_step();

  const namespacet ns(transition_system.symbol_table);
  report_results(cmdline, properties, ns, message.get_message_handler());

  return result;
}

/*******************************************************************\

Function: k_inductiont::induction_base

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int k_inductiont::induction_base()
{
  PRECONDITION(transition_system.trans_expr.has_value());
  message.status() << "Induction Base" << messaget::eom;

  auto solver_wrapper = solver_factory(ns, message.get_message_handler());
  auto &solver = solver_wrapper.stack_decision_procedure();

  // convert the transition system
  ::unwind(
    *transition_system.trans_expr,
    message.get_message_handler(),
    solver,
    bound + 1,
    ns,
    true);

  // convert the properties
  word_level_properties(solver);

  int result = finish_word_level_bmc(solver);

  if(result!=0 && result!=10)
    return result;
  else
    return -1;
}

/*******************************************************************\

Function: k_inductiont::induction_step

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int k_inductiont::induction_step()
{
  PRECONDITION(transition_system.trans_expr.has_value());
  message.status() << "Induction Step" << messaget::eom;

  unsigned no_timeframes=bound+1;

  for(auto &p_it : properties.properties)
  {
    if(p_it.is_disabled() ||
       p_it.is_failure())
      continue;

    auto solver_wrapper = solver_factory(ns, message.get_message_handler());
    auto &solver = solver_wrapper.decision_procedure();

    // *no* initial state
    unwind(
      *transition_system.trans_expr,
      message.get_message_handler(),
      solver,
      no_timeframes,
      ns,
      false);

    exprt property(p_it.expr);

    if(property.id()!=ID_sva_always &&
       property.id()!=ID_AG)
    {
      message.error()
        << "unsupported property - only SVA always or AG implemented"
        << messaget::eom;
      return 1;
    }

    const exprt &p = to_unary_expr(property).op();

    // assumption: time frames 0,...,k-1
    for(unsigned c=0; c<no_timeframes-1; c++)
    {
      exprt tmp=
        instantiate(p, c, no_timeframes-1, ns);
      solver.set_to_true(tmp);
    }
    
    // property: time frame k
    {
      exprt tmp=
        instantiate(p, no_timeframes-1, no_timeframes, ns);
      solver.set_to_false(tmp);
    }

    decision_proceduret::resultt dec_result = solver();

    switch(dec_result)
    {
    case decision_proceduret::resultt::D_SATISFIABLE:
      message.result()
        << "SAT: inductive proof failed, k-induction is inconclusive"
        << messaget::eom;
      p_it.make_unknown();
      break;

    case decision_proceduret::resultt::D_UNSATISFIABLE:
      message.result() << "UNSAT: inductive proof successful, property holds"
                       << messaget::eom;
      p_it.make_success();
      break;

    case decision_proceduret::resultt::D_ERROR:
      message.error() << "Error from decision procedure" << messaget::eom;
      return 2;

    default:
      message.error() << "Unexpected result from decision procedure"
                      << messaget::eom;
      return 1;
    }
  }

  // We return '0' if the property holds,
  // and '10' if it is violated.
  return properties.property_failure() ? 10 : 0;
}
