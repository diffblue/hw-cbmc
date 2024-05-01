/*******************************************************************\

Module: k Induction

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#include "k_induction.h"

#include <util/string2int.h>

#include <temporal-logic/temporal_logic.h>
#include <trans-word-level/instantiate_word_level.h>
#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/unwind.h>

#include "bmc.h"
#include "ebmc_error.h"
#include "ebmc_solver_factory.h"
#include "liveness_to_safety.h"
#include "report_results.h"

#include <fstream>

/*******************************************************************\

   Class: k_inductiont

 Purpose:

\*******************************************************************/

class k_inductiont
{
public:
  k_inductiont(
    std::size_t _k,
    const transition_systemt &_transition_system,
    ebmc_propertiest &_properties,
    const ebmc_solver_factoryt &_solver_factory,
    message_handlert &_message_handler)
    : k(_k),
      transition_system(_transition_system),
      properties(_properties),
      solver_factory(_solver_factory),
      message(_message_handler)
  {
  }

  void operator()();

  static bool
  have_supported_property(const ebmc_propertiest::propertiest &properties)
  {
    for(auto &p : properties)
      if(supported(p))
        return true;
    return false;
  }

protected:
  const std::size_t k;
  const transition_systemt &transition_system;
  ebmc_propertiest &properties;
  const ebmc_solver_factoryt &solver_factory;
  messaget message;

  void induction_base();
  void induction_step();

  static bool supported(const ebmc_propertiest::propertyt &p)
  {
    auto &expr = p.normalized_expr;
    if(expr.id() == ID_sva_always || expr.id() == ID_AG || expr.id() == ID_G)
    {
      // Must be AG p or equivalent.
      auto &op = to_unary_expr(expr).op();
      return !has_temporal_operator(op);
    }
    else
      return false;
  }
};

/*******************************************************************\

Function: do_k_induction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void k_induction(
  std::size_t k,
  const transition_systemt &transition_system,
  ebmc_propertiest &properties,
  const ebmc_solver_factoryt &solver_factory,
  message_handlert &message_handler)
{
  k_inductiont(
    k, transition_system, properties, solver_factory, message_handler)();
}

/*******************************************************************\

Function: do_k_induction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int do_k_induction(
  const cmdlinet &cmdline,
  ui_message_handlert &message_handler)
{
  std::size_t k = [&cmdline, &message_handler]() -> std::size_t {
    if(!cmdline.isset("bound"))
    {
      messaget message(message_handler);
      message.warning() << "using 1-induction" << messaget::eom;
      return 1;
    }
    else
      return unsafe_string2unsigned(cmdline.get_value("bound"));
  }();

  auto transition_system = get_transition_system(cmdline, message_handler);

  auto properties = ebmc_propertiest::from_command_line(
    cmdline, transition_system, message_handler);

  if(properties.properties.empty())
    throw ebmc_errort() << "no properties";

  // liveness to safety translation, if requested
  if(cmdline.isset("liveness-to-safety"))
    liveness_to_safety(transition_system, properties);

  // Are there any properties suitable for k-induction?
  // Fail early if not.
  if(!k_inductiont::have_supported_property(properties.properties))
  {
    throw ebmc_errort() << "there is no property suitable for k-induction";
  }

  auto solver_factory = ebmc_solver_factory(cmdline);

  k_induction(
    k, transition_system, properties, solver_factory, message_handler);

  const namespacet ns(transition_system.symbol_table);
  report_results(cmdline, properties, ns, message_handler);

  // We return '0' if all properties are proved,
  // and '10' otherwise.
  return properties.all_properties_proved() ? 0 : 10;
}

/*******************************************************************\

Function: k_inductiont::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void k_inductiont::operator()()
{
  // Fail unsupported properties
  for(auto &property : properties.properties)
  {
    if(!supported(property))
      property.failure("property unsupported by k-induction");
  }

  // do induction base
  induction_base();

  // do induction step
  induction_step();
}

/*******************************************************************\

Function: k_inductiont::induction_base

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void k_inductiont::induction_base()
{
  message.status() << "Induction Base" << messaget::eom;

  bmc(
    k,
    false,
    transition_system,
    properties,
    solver_factory,
    message.get_message_handler());
}

/*******************************************************************\

Function: k_inductiont::induction_step

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void k_inductiont::induction_step()
{
  message.status() << "Induction Step" << messaget::eom;

  const std::size_t no_timeframes = k + 1;
  const namespacet ns(transition_system.symbol_table);

  for(auto &p_it : properties.properties)
  {
    if(p_it.is_disabled() || p_it.is_failure() || p_it.is_assumed())
      continue;

    // If it's not failed, then it's supported.
    DATA_INVARIANT(supported(p_it), "property must be supported");

    // Do not run the step case for properties that have
    // failed the base case already. Properties may pass the step
    // case, but are still false when the base case fails.
    if(p_it.is_refuted())
      continue;

    auto solver_wrapper = solver_factory(ns, message.get_message_handler());
    auto &solver = solver_wrapper.decision_procedure();

    // *no* initial state
    unwind(
      transition_system.trans_expr,
      message.get_message_handler(),
      solver,
      no_timeframes,
      ns,
      false);

    // add all assumptions for all time frames
    for(auto &property : properties.properties)
      if(property.is_assumed())
      {
        const exprt &p = to_unary_expr(property.normalized_expr).op();
        for(std::size_t c = 0; c < no_timeframes; c++)
        {
          exprt tmp = instantiate(p, c, no_timeframes, ns);
          solver.set_to_true(tmp);
        }
      }

    const exprt property(p_it.normalized_expr);
    const exprt &p = to_unary_expr(property).op();

    // assumption: time frames 0,...,k-1
    for(std::size_t c = 0; c < no_timeframes - 1; c++)
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
      p_it.inconclusive();
      break;

    case decision_proceduret::resultt::D_UNSATISFIABLE:
      message.result() << "UNSAT: inductive proof successful, property holds"
                       << messaget::eom;
      p_it.proved();
      break;

    case decision_proceduret::resultt::D_ERROR:
      throw ebmc_errort() << "Error from decision procedure";

    default:
      throw ebmc_errort() << "Unexpected result from decision procedure";
    }
  }
}
