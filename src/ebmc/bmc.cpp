/*******************************************************************\

Module: Bounded Model Checking

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "bmc.h"

#include <solvers/prop/literal_expr.h>
#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/unwind.h>

#include "ebmc_error.h"

#include <chrono>
#include <fstream>

void bmc(
  std::size_t bound,
  bool convert_only,
  const transition_systemt &transition_system,
  ebmc_propertiest &properties,
  const ebmc_solver_factoryt &solver_factory,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  message.status() << "Generating Decision Problem" << messaget::eom;

  // convert the transition system
  const namespacet ns(transition_system.symbol_table);

  auto solver_wrapper = solver_factory(ns, message_handler);
  auto &solver = solver_wrapper.stack_decision_procedure();

  ::unwind(
    transition_system.trans_expr, message_handler, solver, bound + 1, ns, true);

  // convert the properties
  message.status() << "Properties" << messaget::eom;

  for(auto &property : properties.properties)
  {
    if(property.is_disabled())
      continue;

    ::property(
      property.expr,
      property.timeframe_handles,
      message_handler,
      solver,
      bound + 1,
      ns);
  }

  // lasso constraints, if needed
  if(properties.requires_lasso_constraints())
  {
    message.status() << "Adding lasso constraints" << messaget::eom;
    lasso_constraints(
      solver, bound + 1, ns, transition_system.main_symbol->name);
  }

  if(convert_only)
  {
    for(const auto &property : properties.properties)
    {
      if(!property.is_disabled())
        solver.set_to_false(conjunction(property.timeframe_handles));
    }
  }
  else
  {
    message.status() << "Solving with " << solver.decision_procedure_text()
                     << messaget::eom;

    auto sat_start_time = std::chrono::steady_clock::now();

    // Use assumptions to check the properties separately

    for(auto &property : properties.properties)
    {
      if(property.is_disabled())
        continue;

      message.status() << "Checking " << property.name << messaget::eom;

      auto constraint = not_exprt(conjunction(property.timeframe_handles));
      auto handle = solver.handle(constraint);
      if(handle.is_true())
        solver.push({literal_exprt(const_literal(true))});
      else if(handle.is_false())
        solver.push({literal_exprt(const_literal(false))});
      else
        solver.push({solver.handle(constraint)});

      decision_proceduret::resultt dec_result = solver();

      solver.pop();

      switch(dec_result)
      {
      case decision_proceduret::resultt::D_SATISFIABLE:
        property.refuted();
        message.result() << "SAT: counterexample found" << messaget::eom;

        property.counterexample = compute_trans_trace(
          property.timeframe_handles,
          solver,
          bound + 1,
          ns,
          transition_system.main_symbol->name);
        break;

      case decision_proceduret::resultt::D_UNSATISFIABLE:
        message.result() << "UNSAT: No counterexample found within bound"
                         << messaget::eom;
        property.proved_with_bound(bound);
        break;

      case decision_proceduret::resultt::D_ERROR:
        message.error() << "Error from decision procedure" << messaget::eom;
        property.failure();
        break;

      default:
        property.failure();
        throw ebmc_errort() << "Unexpected result from decision procedure";
      }
    }

    auto sat_stop_time = std::chrono::steady_clock::now();

    message.statistics()
      << "Solver time: "
      << std::chrono::duration<double>(sat_stop_time - sat_start_time).count()
      << messaget::eom;
  }
}
