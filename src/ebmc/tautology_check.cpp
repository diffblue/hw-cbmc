/*******************************************************************\

Module: Property Tautology Check

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "tautology_check.h"

#include <util/namespace.h>

#include <temporal-logic/ctl.h>
#include <temporal-logic/ltl.h>

static bool is_tautology(
  const exprt &expr,
  const ebmc_solver_factoryt &solver_factory,
  message_handlert &message_handler)
{
  auto is_tautology_p = [&solver_factory, &message_handler](const exprt &expr)
  {
    // rec. call
    return is_tautology(expr, solver_factory, message_handler);
  };

  if(!has_temporal_operator(expr))
  {
    // State predicate. Let's ask the SAT solver.
    if(expr.is_true())
      return true;

    symbol_tablet symbol_table;
    namespacet ns{symbol_table};
    auto solver = solver_factory(ns, message_handler);

    switch(solver.decision_procedure()(not_exprt{expr}))
    {
    case decision_proceduret::resultt::D_UNSATISFIABLE:
      return true;

    case decision_proceduret::resultt::D_SATISFIABLE:
    case decision_proceduret::resultt::D_ERROR:
    default:
      return false;
    }
  }
  else // has temporal operator
  {
    if(expr.id() == ID_G && is_tautology_p(to_G_expr(expr).op()))
      return true;
    else if(expr.id() == ID_F && is_tautology_p(to_F_expr(expr).op()))
      return true;
    else if(expr.id() == ID_X && is_tautology_p(to_X_expr(expr).op()))
      return true;
    else if(expr.id() == ID_AG && is_tautology_p(to_AG_expr(expr).op()))
      return true;
    else if(expr.id() == ID_AF && is_tautology_p(to_AF_expr(expr).op()))
      return true;
    else if(expr.id() == ID_AX && is_tautology_p(to_AX_expr(expr).op()))
      return true;
    else // other temporal operator
      return false;
  }
}

property_checker_resultt tautology_check(
  const cmdlinet &,
  const ebmc_propertiest &properties,
  const ebmc_solver_factoryt &solver_factory,
  message_handlert &message_handler)
{
  property_checker_resultt result{properties};

  for(auto &property : result.properties)
  {
    if(property.is_unknown())
    {
      if(is_tautology(
           property.normalized_expr, solver_factory, message_handler))
      {
        property.proved("tautology");
      }
    }
  }

  return result;
}
