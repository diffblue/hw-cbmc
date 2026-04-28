/*******************************************************************\

Module: Transition Property Engine

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "transition_property.h"

#include <temporal-logic/ltl.h>
#include <temporal-logic/sva_to_ltl.h>
#include <temporal-logic/temporal_logic.h>
#include <trans-word-level/instantiate_word_level.h>
#include <trans-word-level/next_symbol.h>
#include <trans-word-level/unwind.h>

#include "ebmc_error.h"

/// Returns true iff the given LTL property is
/// any non-modal expression and expressions that
/// contain non-nested use of LTL X.
bool is_transition_property_aux(const exprt &expr)
{
  if(!has_temporal_operator(expr))
    return true;
  else if(
    expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_implies ||
    expr.id() == ID_not)
  {
    for(auto &op : expr.operands())
      if(!is_transition_property_aux(op))
        return false;
    return true;
  }
  else if(expr.id() == ID_X)
  {
    return !has_temporal_operator(to_X_expr(expr).op());
  }
  else
    return false;
}

/// Is the given property a "transition property"? They can
/// be characterized syntactically as G Q where
///   Q: p, Q ∧ Q, ¬Q, X p
/// where p does not contain any temporal operator.
bool is_transition_property(const exprt &expr)
{
  // SVA?
  if(is_LTL(expr))
  {
    // Must be G body.
    if(expr.id() != ID_G)
      return false;

    return is_transition_property_aux(to_G_expr(expr).op());
  }
  else if(is_SVA(expr))
  {
    // Convert SVA to LTL first.
    try
    {
      auto ltl_expr = SVA_to_LTL(expr);
      return is_transition_property(ltl_expr);
    }
    catch(const sva_to_ltl_unsupportedt &)
    {
      return false;
    }
  }
  else
    return false;
}

property_checker_resultt transition_property(
  const transition_systemt &transition_system,
  const ebmc_propertiest &properties_in,
  const ebmc_solver_factoryt &solver_factory,
  message_handlert &message_handler)
{
  auto properties = properties_in; // copy

  // Is this engine applicable?
  bool have_property = false;

  for(auto &property : properties.properties)
  {
    if(!property.is_unknown())
      continue;

    if(is_transition_property(property.normalized_expr))
      have_property = true;
    else
      property.unsupported("unsupported by transition property engine");
  }

  if(!have_property)
    return property_checker_resultt{properties};

  messaget message{message_handler};
  const namespacet ns{transition_system.symbol_table};
  auto solver_wrapper = solver_factory(ns, message_handler);
  auto &solver = solver_wrapper.decision_procedure();

  message.status() << "Checking transition properties" << messaget::eom;

  // We can prove "transition properties" G Q by checking if the transition
  // relation implies Q. This uses the standard assumption that the transition
  // relation is left-total (otherwise there could be initial states without
  // successsor that yield traces with one state that refute G Q).
  //
  // Note that transition properties are not in general transition invariants;
  // they contain the transition relation, but not the transitive closure of
  // the transition relation.

  // One transition: 2 timeframes, no initial state.
  unwind(
    transition_system.trans_expr,
    message_handler,
    solver,
    2, // no_timeframes
    ns,
    false); // no initial state constraint

  std::map<irep_idt, exprt> handles;

  for(auto &property : properties.properties)
  {
    if(!property.is_unknown())
      continue;

    // Instantiate property, for two timeframes
    auto obligations =
      ::property(property.normalized_expr, false, message_handler, 2);
    auto constraint = not_exprt{conjunction(obligations)};
    handles[property.identifier] = solver.handle(constraint);
  }

  // Check the properties incrementally
  for(auto &property : properties.properties)
  {
    auto handle_it = handles.find(property.identifier);
    if(handle_it == handles.end())
      continue;

    message.status() << "Checking " << property.name
                     << " using transition property engine" << messaget::eom;

    switch(solver(handle_it->second))
    {
    case decision_proceduret::resultt::D_UNSATISFIABLE:
      message.result() << "UNSAT: property holds for all transitions"
                       << messaget::eom;
      if(property.is_exists_path())
        property.refuted("transition property");
      else
        property.proved("transition property");
      break;

    case decision_proceduret::resultt::D_SATISFIABLE:
      message.result() << "SAT: transition property check is inconclusive"
                       << messaget::eom;
      property.inconclusive();
      break;

    case decision_proceduret::resultt::D_ERROR:
      throw ebmc_errort() << "Error from decision procedure";

    default:
      throw ebmc_errort() << "Unexpected result from decision procedure";
    }
  }

  return property_checker_resultt{properties};
}
