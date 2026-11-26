/*******************************************************************\

Module: Bounded Model Checking

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "bmc.h"

#include <solvers/prop/literal_expr.h>
#include <solvers/prop/prop_conv_solver.h>
#include <trans-word-level/cone_of_influence.h>
#include <trans-word-level/lasso.h>
#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/unwind.h>

#include "ebmc_error.h"

#include <algorithm>
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

/// Returns the transition relation to be unwound, reduced to the
/// cone of influence of the properties if \p cone_of_influence is set.
static transt bmc_trans(
  bool cone_of_influence,
  const transition_systemt &transition_system,
  const ebmc_propertiest &properties,
  messaget &message)
{
  if(!cone_of_influence)
    return transition_system.trans_expr;

  auto coi_result = ::cone_of_influence(
    transition_system.trans_expr, properties.active_expressions());
  coi_result.report(message);
  return std::move(coi_result.trans);
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
  bool cone_of_influence,
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

  // Reduce the transition system to the cone of influence
  // of the properties, if asked to do so.
  const auto trans_expr =
    bmc_trans(cone_of_influence, transition_system, properties, message);

  message.status() << "Generating Decision Problem" << messaget::eom;

  // convert the transition system
  const namespacet ns(transition_system.symbol_table);

  auto solver_wrapper = solver_factory(ns, message_handler);
  auto &solver = solver_wrapper.decision_procedure();
  auto no_timeframes = bound + 1;

  word_level_unwind_optionst unwind_options;
  unwind_options.add_initial_state = true;
  ::unwind(
    trans_expr, message_handler, solver, no_timeframes, ns, unwind_options);

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

    auto obligations = ::property(
      property.normalized_expr,
      !property.is_exists_path(),
      message_handler,
      no_timeframes);

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

/// Solves the BMC problem for the given bound, for all properties
/// that are still unknown. The obligations for this bound are
/// conditional on \p activation.
/// \return false if the solver reported an error
static bool bmc_incremental_solve(
  std::size_t bound,
  const exprt &activation,
  bool bmc_with_assumptions,
  const transition_systemt &transition_system,
  ebmc_propertiest &properties,
  decision_proceduret &solver,
  messaget &message)
{
  const namespacet ns(transition_system.symbol_table);
  const auto no_timeframes = bound + 1;

  auto is_open = [](const ebmc_propertiest::propertyt &property)
  { return property.is_unknown(); };

  auto record_trace = [&](ebmc_propertiest::propertyt &property)
  {
    if(property.is_exists_path())
    {
      property.proved();
      message.result() << "SAT: path found for " << property.name
                       << messaget::eom;
    }
    else // universal path property
    {
      property.refuted();
      message.result() << "SAT: counterexample found for " << property.name
                       << messaget::eom;
    }

    property.witness_trace = compute_trans_trace(
      property.timeframe_handles,
      solver,
      no_timeframes,
      ns,
      transition_system.main_symbol->name);
  };

  auto fail_open_properties = [&]()
  {
    for(auto &property : properties.properties)
      if(is_open(property))
        property.failure();
  };

  if(bmc_with_assumptions)
  {
    // check the properties separately
    for(auto &property : properties.properties)
    {
      if(!is_open(property))
        continue;

      message.status() << "Checking " << property.name << messaget::eom;

      auto assumption = and_exprt{
        activation, not_exprt{conjunction(property.timeframe_handles)}};

      switch(solver(assumption))
      {
      case decision_proceduret::resultt::D_SATISFIABLE:
        record_trace(property);
        break;

      case decision_proceduret::resultt::D_UNSATISFIABLE:
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

    return true;
  }

  auto trace_found = [&solver](const ebmc_propertiest::propertyt &property)
  {
    for(auto &h : property.timeframe_handles)
      if(solver.get(h).is_false())
        return true;
    return false;
  };

  // Ask for a trace that violates at least one of the open properties,
  // until there is none.
  while(true)
  {
    exprt::operandst disjuncts;

    for(auto &property : properties.properties)
      if(is_open(property))
        for(auto &h : property.timeframe_handles)
          disjuncts.push_back(not_exprt{h});

    if(disjuncts.empty())
      return true;

    auto assumption = and_exprt{activation, disjunction(disjuncts)};

    switch(solver(assumption))
    {
    case decision_proceduret::resultt::D_SATISFIABLE:
    {
      bool found = false;

      for(auto &property : properties.properties)
      {
        if(is_open(property) && trace_found(property))
        {
          record_trace(property);
          found = true;
        }
      }

      if(!found)
      {
        fail_open_properties();
        throw ebmc_errort() << "decision procedure returned a model that "
                               "does not violate any property";
      }
    }
    break; // next iteration of while loop

    case decision_proceduret::resultt::D_UNSATISFIABLE:
      return true;

    case decision_proceduret::resultt::D_ERROR:
      fail_open_properties();
      message.error() << "Error from decision procedure" << messaget::eom;
      return false;

    default:
      fail_open_properties();
      throw ebmc_errort() << "Unexpected result from decision procedure";
    }
  }
}

property_checker_resultt bmc_incremental(
  std::size_t max_bound,
  bool bmc_with_assumptions,
  bool cone_of_influence,
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

  const auto trans_expr =
    bmc_trans(cone_of_influence, transition_system, properties, message);

  const namespacet ns(transition_system.symbol_table);

  auto solver_wrapper = solver_factory(ns, message_handler);
  auto &solver = solver_wrapper.decision_procedure();

  // We add clauses to the SAT solver after it has been run.
  // A SAT solver with preprocessing (e.g., MiniSat's SimpSolver)
  // may have eliminated any variable that is not frozen, and new
  // clauses must not mention eliminated variables. The new clauses
  // can reuse any literal that the propositional encoding has cached
  // (symbols in any timeframe, subexpressions shared between
  // obligations of different bounds). We therefore freeze all
  // literals that the encoding hands out. Auxiliary literals that are
  // internal to the encoding of an expression are never referenced
  // again and remain subject to elimination.
  auto prop_conv_solver = dynamic_cast<prop_conv_solvert *>(&solver);
  if(prop_conv_solver == nullptr)
    throw ebmc_errort() << "--max-bound requires a SAT-based solver; it is not "
                           "supported with SMT solvers";

  prop_conv_solver->set_all_frozen();

  message.status() << "Solving with " << solver.decision_procedure_text()
                   << " incrementally up to bound " << max_bound
                   << messaget::eom;

  std::chrono::duration<double> solver_time{0};

  bool requires_lasso_constraints = false;
  std::size_t unwound_timeframes = 0;
  std::size_t lasso_timeframes = 0;

  // We start with bound 0, i.e., a single timeframe, as --bound 0 does.
  // A property is refuted at the smallest bound with a counterexample,
  // and hence, the counterexample is a shortest one.
  for(std::size_t bound = 0; bound <= max_bound; bound++)
  {
    bool have_unknown_property = std::any_of(
      properties.properties.begin(),
      properties.properties.end(),
      [](const ebmc_propertiest::propertyt &p) { return p.is_unknown(); });

    // stop early once all properties are decided
    if(!have_unknown_property)
      break;

    const auto no_timeframes = bound + 1;

    message.status() << "Doing BMC with bound " << bound << messaget::eom;

    // Add the new timeframe. The constraints for the earlier
    // timeframes do not depend on the bound, and are reused.
    word_level_unwind_optionst unwind_options;
    unwind_options.add_initial_state = true;
    ::unwind(
      trans_expr,
      message_handler,
      solver,
      unwound_timeframes,
      no_timeframes,
      ns,
      unwind_options);
    unwound_timeframes = no_timeframes;

    // The property obligations depend on the bound (e.g., weak
    // semantics at the end of the bound, pending matches, lassos).
    // They are made conditional on a fresh activation literal, which
    // is retired after this bound has been solved.
    const exprt activation = solver.handle(symbol_exprt{
      "ebmc::bmc::activation::" + std::to_string(bound), bool_typet{}});

    for(auto &property : properties.properties)
    {
      if(!property.is_unknown() && !property.is_assumed())
        continue;

      auto obligations = ::property(
        property.normalized_expr,
        !property.is_exists_path(),
        message_handler,
        no_timeframes);

      if(uses_lasso_symbol(obligations))
        requires_lasso_constraints = true;

      property.timeframe_handles = handles(obligations, solver);

      // Assumptions constrain this bound only.
      if(property.is_assumed())
      {
        solver.set_to_true(
          implies_exprt{activation, conjunction(property.timeframe_handles)});
      }
    }

    // The lasso constraints define the lasso symbols, and hence,
    // can be added for all timeframes unconditionally.
    if(requires_lasso_constraints && lasso_timeframes < no_timeframes)
    {
      lasso_constraints(
        solver,
        lasso_timeframes,
        no_timeframes,
        ns,
        transition_system.main_symbol->name);
      lasso_timeframes = no_timeframes;
    }

    auto sat_start_time = std::chrono::steady_clock::now();

    bool ok = bmc_incremental_solve(
      bound,
      activation,
      bmc_with_assumptions,
      transition_system,
      properties,
      solver,
      message);

    solver_time += std::chrono::steady_clock::now() - sat_start_time;

    if(!ok)
      break;

    // retire the obligations of this bound
    solver.set_to_true(not_exprt{activation});
  }

  // The properties that remain unknown hold up to the maximum bound.
  for(auto &property : properties.properties)
  {
    if(property.is_unknown())
    {
      if(property.is_exists_path())
        property.refuted_with_bound(max_bound);
      else
        property.proved_with_bound(max_bound);
    }
  }

  message.statistics() << "Solver time: " << solver_time.count()
                       << messaget::eom;

  return property_checker_resultt{std::move(properties)};
}
