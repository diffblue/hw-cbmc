/*******************************************************************\

Module: Bounded Model Checking

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "bmc.h"

#include <solvers/prop/literal_expr.h>
#include <trans-word-level/lasso.h>
#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/unwind.h>

#include "ebmc_error.h"

#include <chrono>
#include <fstream>

void bmc_with_assumptions(
  std::size_t bound,
  const transition_systemt &transition_system,
  ebmc_propertiest &properties,
  decision_proceduret &solver,
  message_handlert &message_handler)
{
  messaget message(message_handler);
  const namespacet ns(transition_system.symbol_table);

  // Use assumptions to check the properties separately

  for(auto &property : properties.properties)
  {
    if(property.is_disabled() || property.is_failure() || property.is_assumed())
    {
      continue;
    }

    message.status() << "Checking " << property.name << messaget::eom;

    auto assumption = not_exprt{conjunction(property.timeframe_handles)};

    decision_proceduret::resultt dec_result = solver(assumption);

    switch(dec_result)
    {
    case decision_proceduret::resultt::D_SATISFIABLE:
      if(property.is_exists_path())
      {
        property.proved();
        message.result() << "SAT: path found" << messaget::eom;
      }
      else // universal path property
      {
        property.refuted();
        message.result() << "SAT: counterexample found" << messaget::eom;
      }

      property.witness_trace = compute_trans_trace(
        property.timeframe_handles,
        solver,
        bound + 1,
        ns,
        transition_system.main_symbol->name);
      break;

    case decision_proceduret::resultt::D_UNSATISFIABLE:
      if(property.is_exists_path())
      {
        message.result() << "UNSAT: No path found within bound"
                         << messaget::eom;
        property.refuted_with_bound(bound);
      }
      else // universal path property
      {
        message.result() << "UNSAT: No counterexample found within bound"
                         << messaget::eom;
        property.proved_with_bound(bound);
      }
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
}

/// VMCAI 2009 Query-driven program testing,
/// "iterative constraint strengthening"
void bmc_with_iterative_constraint_strengthening(
  std::size_t bound,
  const transition_systemt &transition_system,
  ebmc_propertiest &properties,
  decision_proceduret &solver,
  message_handlert &message_handler)
{
  messaget message(message_handler);
  const namespacet ns(transition_system.symbol_table);

  auto trace_found = [&solver](const ebmc_propertiest::propertyt &property)
  {
    for(auto &h : property.timeframe_handles)
      if(solver.get(h).is_false())
        return true;
    return false;
  };

  while(true)
  {
    // At least one of the remaining properties
    // should be falsified.
    exprt::operandst disjuncts;

    for(auto &property : properties.properties)
    {
      if(property.is_unknown())
      {
        for(auto &h : property.timeframe_handles)
          disjuncts.push_back(not_exprt{h});
      }
    }

    // This constraint is strenthened in each iteration.
    solver.set_to_true(disjunction(disjuncts));

    decision_proceduret::resultt dec_result = solver();

    switch(dec_result)
    {
    case decision_proceduret::resultt::D_SATISFIABLE:
      // Found a trace for at least one further property with unknown state
      message.result() << "SAT: path found" << messaget::eom;

      for(auto &property : properties.properties)
      {
        if(property.is_unknown() && trace_found(property))
        {
          if(property.is_exists_path())
            property.proved();
          else // universal path property
            property.refuted();

          property.witness_trace = compute_trans_trace(
            property.timeframe_handles,
            solver,
            bound + 1,
            ns,
            transition_system.main_symbol->name);
        }
      }
      break; // next iteration of while loop

    case decision_proceduret::resultt::D_UNSATISFIABLE:
      message.result() << "UNSAT: No path found within bound" << messaget::eom;

      for(auto &property : properties.properties)
      {
        if(property.is_unknown())
        {
          if(property.is_exists_path())
            property.refuted_with_bound(bound);
          else // universal path property
            property.proved_with_bound(bound);
        }
      }
      return;

    case decision_proceduret::resultt::D_ERROR:
      for(auto &property : properties.properties)
      {
        if(property.is_unknown())
          property.failure();
      }
      message.error() << "Error from decision procedure" << messaget::eom;
      return;

    default:
      for(auto &property : properties.properties)
      {
        if(property.is_unknown())
          property.failure();
      }
      throw ebmc_errort() << "Unexpected result from decision procedure";
    }
  }
}

/// Extension of solver.handle(...) from expressions to vectors of expressions
static exprt::operandst
handles(const exprt::operandst &exprs, decision_proceduret &solver)
{
  exprt::operandst result;
  result.reserve(exprs.size());
  for(auto &expr : exprs)
    result.push_back(solver.handle(expr));
  return result;
}

static bool have_supported_property(ebmc_propertiest &properties)
{
  bool have_supported = false;

  for(auto &property : properties.properties)
  {
    if(property.is_disabled() || property.is_failure())
      continue;

    // Is it supported by the BMC engine?
    if(bmc_supports_property(property.normalized_expr))
      have_supported = true;
    else
      property.failure("property not supported by BMC engine");
  }

  return have_supported;
}

property_checker_resultt bmc(
  std::size_t bound,
  bool convert_only,
  bool bmc_with_assumptions,
  const transition_systemt &transition_system,
  const ebmc_propertiest &properties_in,
  const ebmc_solver_factoryt &solver_factory,
  message_handlert &message_handler)
{
  // copy
  ebmc_propertiest properties = properties_in;

  messaget message(message_handler);

  // exit early if there is no supported property
  if(!have_supported_property(properties))
  {
    message.status() << "No supported property" << messaget::eom;
    return property_checker_resultt{std::move(properties)};
  }

  message.status() << "Generating Decision Problem" << messaget::eom;

  // convert the transition system
  const namespacet ns(transition_system.symbol_table);

  auto solver_wrapper = solver_factory(ns, message_handler);
  auto &solver = solver_wrapper.decision_procedure();
  auto no_timeframes = bound + 1;

  ::unwind(
    transition_system.trans_expr,
    message_handler,
    solver,
    no_timeframes,
    ns,
    true);

  // convert the properties
  message.status() << "Properties" << messaget::eom;

  bool requires_lasso_constraints = false;

  for(auto &property : properties.properties)
  {
    if(property.is_disabled() || property.is_failure())
      continue;

    // Is it supported by the BMC engine?
    if(!bmc_supports_property(property.normalized_expr))
    {
      property.failure("property not supported by BMC engine");
      continue;
    }

    auto obligations =
      ::property(property.normalized_expr, message_handler, no_timeframes);

    if(uses_lasso_symbol(obligations))
      requires_lasso_constraints = true;

    property.timeframe_handles = handles(obligations, solver);

    // If it's an assumption, then add it as constraint.
    if(property.is_assumed())
      solver.set_to_true(conjunction(property.timeframe_handles));
  }

  // lasso constraints, if needed
  if(requires_lasso_constraints)
  {
    message.status() << "Adding lasso constraints" << messaget::eom;
    lasso_constraints(
      solver, no_timeframes, ns, transition_system.main_symbol->name);
  }

  if(convert_only)
  {
    // At least one property must be violated in at least one
    // timeframe.
    exprt::operandst disjuncts;

    for(const auto &property : properties.properties)
    {
      if(property.is_assumed())
      {
        // already added as constraint above
      }
      else if(!property.is_disabled())
      {
        for(auto &h : property.timeframe_handles)
          disjuncts.push_back(not_exprt{h});
      }
    }

    solver.set_to_true(disjunction(disjuncts));

    // Call decision_proceduret::dec_solve to finish the conversion
    // process.
    (void)solver();
  }
  else
  {
    message.status() << "Solving with " << solver.decision_procedure_text()
                     << messaget::eom;

    auto sat_start_time = std::chrono::steady_clock::now();

    if(bmc_with_assumptions)
    {
      ::bmc_with_assumptions(
        bound, transition_system, properties, solver, message_handler);
    }
    else
    {
      ::bmc_with_iterative_constraint_strengthening(
        bound, transition_system, properties, solver, message_handler);
    }

    auto sat_stop_time = std::chrono::steady_clock::now();

    message.statistics()
      << "Solver time: "
      << std::chrono::duration<double>(sat_stop_time - sat_start_time).count()
      << messaget::eom;
  }

  return property_checker_resultt{std::move(properties)};
}
