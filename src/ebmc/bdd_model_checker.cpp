/*******************************************************************\

Module: BDD-based CTL Model Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bdd_model_checker.h"

#include <util/std_expr.h>

#include <solvers/prop/literal_expr.h>
#include <temporal-logic/ctl.h>

#include <algorithm>

using BDD = mini_bddt;

// forward declarations of local helpers
static BDD EX(const bdd_modelt &, BDD);
static BDD fixedpoint(std::function<BDD(BDD)>, BDD);

/*******************************************************************\

Function: current_to_next

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static BDD current_to_next(const bdd_modelt &model, const BDD &bdd)
{
  BDD tmp = bdd;
  for(const auto &v : model.vars)
    tmp = substitute(tmp, v.current.var(), v.next);
  return tmp;
}

/*******************************************************************\

Function: project_next

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static BDD project_next(const bdd_modelt &model, const BDD &bdd)
{
  BDD tmp = bdd;
  for(const auto &v : model.vars)
    tmp = exists(tmp, v.next.var());
  return tmp;
}

/*******************************************************************\

Function: EX

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static BDD EX(const bdd_modelt &model, BDD f)
{
  for(const auto &c : model.constraints)
    f = f & c;

  BDD p_next = current_to_next(model, f);

  BDD conjunction = p_next;
  for(const auto &t : model.transition)
    conjunction = conjunction & t;
  for(const auto &c : model.constraints)
    conjunction = conjunction & c;

  return project_next(model, conjunction);
}

/*******************************************************************\

Function: AX

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static BDD AX(const bdd_modelt &model, BDD f)
{
  return !EX(model, !f);
}

/*******************************************************************\

Function: fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static BDD fixedpoint(std::function<BDD(BDD)> tau, BDD x)
{
  while(true)
  {
    BDD image = tau(x);
    if((image == x).is_true())
      return x;
    x = image;
  }
}

/*******************************************************************\

Function: EG

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static BDD EG(const bdd_modelt &model, BDD f)
{
  return fixedpoint([&](BDD x) { return x & EX(model, x); }, f);
}

/*******************************************************************\

Function: EF

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static BDD EF(const bdd_modelt &model, BDD f)
{
  return fixedpoint([&](BDD x) { return x | EX(model, x); }, f);
}

/*******************************************************************\

Function: EU

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static BDD EU(const bdd_modelt &model, BDD f1, BDD f2)
{
  return fixedpoint(
    [&](BDD x) { return x | f2 | (f1 & EX(model, x)); }, model.mgr.False());
}

/*******************************************************************\

Function: AU

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static BDD AU(const bdd_modelt &model, BDD f1, BDD f2)
{
  return fixedpoint(
    [&](BDD x) { return x | f2 | (f1 & AX(model, x)); }, model.mgr.False());
}

/*******************************************************************\

Function: bdd_ctl

  Inputs: a CTL expression with literal_exprt atomic propositions

 Outputs: a BDD for the set of states satisfying the expression

 Purpose: compute states that satisfy a CTL property

\*******************************************************************/

mini_bddt bdd_ctl(
  const bdd_modelt &model,
  const exprt &expr,
  const std::map<unsigned, mini_bddt> &atomic_proposition_bdds,
  message_handlert &message_handler)
{
  auto &mgr = model.mgr;

  if(expr.is_true())
    return mgr.True();
  else if(expr.is_false())
    return mgr.False();
  else if(expr.id() == ID_not)
  {
    return !bdd_ctl(
      model, to_not_expr(expr).op(), atomic_proposition_bdds, message_handler);
  }
  else if(expr.id() == ID_implies)
  {
    return (!bdd_ctl(
             model,
             to_binary_expr(expr).lhs(),
             atomic_proposition_bdds,
             message_handler)) |
           bdd_ctl(
             model,
             to_binary_expr(expr).rhs(),
             atomic_proposition_bdds,
             message_handler);
  }
  else if(expr.id() == ID_and)
  {
    BDD result = mgr.True();
    for(const auto &op : expr.operands())
      result =
        result & bdd_ctl(model, op, atomic_proposition_bdds, message_handler);
    return result;
  }
  else if(expr.id() == ID_or)
  {
    BDD result = mgr.False();
    for(const auto &op : expr.operands())
      result =
        result | bdd_ctl(model, op, atomic_proposition_bdds, message_handler);
    return result;
  }
  else if(
    expr.id() == ID_equal && to_equal_expr(expr).lhs().type().id() == ID_bool)
  {
    return !(
      bdd_ctl(
        model,
        to_binary_expr(expr).lhs(),
        atomic_proposition_bdds,
        message_handler) ^
      bdd_ctl(
        model,
        to_binary_expr(expr).rhs(),
        atomic_proposition_bdds,
        message_handler));
  }
  else if(expr.id() == ID_EX)
  {
    return EX(
      model,
      bdd_ctl(
        model,
        to_EX_expr(expr).op(),
        atomic_proposition_bdds,
        message_handler));
  }
  else if(expr.id() == ID_EF)
  {
    return EF(
      model,
      bdd_ctl(
        model,
        to_EF_expr(expr).op(),
        atomic_proposition_bdds,
        message_handler));
  }
  else if(expr.id() == ID_EG)
  {
    return EG(
      model,
      bdd_ctl(
        model,
        to_EG_expr(expr).op(),
        atomic_proposition_bdds,
        message_handler));
  }
  else if(expr.id() == ID_AX)
  {
    return AX(
      model,
      bdd_ctl(
        model,
        to_AX_expr(expr).op(),
        atomic_proposition_bdds,
        message_handler));
  }
  else if(expr.id() == ID_AF)
  {
    // AF f = !EG(!f)
    return !EG(
      model,
      !bdd_ctl(
        model,
        to_AF_expr(expr).op(),
        atomic_proposition_bdds,
        message_handler));
  }
  else if(expr.id() == ID_AG)
  {
    // AG f = !EF(!f)
    return !EF(
      model,
      !bdd_ctl(
        model,
        to_AG_expr(expr).op(),
        atomic_proposition_bdds,
        message_handler));
  }
  else if(expr.id() == ID_EU)
  {
    auto &EU_expr = to_EU_expr(expr);
    return EU(
      model,
      bdd_ctl(model, EU_expr.lhs(), atomic_proposition_bdds, message_handler),
      bdd_ctl(model, EU_expr.rhs(), atomic_proposition_bdds, message_handler));
  }
  else if(expr.id() == ID_AU)
  {
    auto &AU_expr = to_AU_expr(expr);
    return AU(
      model,
      bdd_ctl(model, AU_expr.lhs(), atomic_proposition_bdds, message_handler),
      bdd_ctl(model, AU_expr.rhs(), atomic_proposition_bdds, message_handler));
  }
  else if(expr.id() == ID_ER)
  {
    // ER(f1, f2) = !AU(!f1, !f2)
    auto &ER_expr = to_ER_expr(expr);
    return !AU(
      model,
      !bdd_ctl(model, ER_expr.lhs(), atomic_proposition_bdds, message_handler),
      !bdd_ctl(model, ER_expr.rhs(), atomic_proposition_bdds, message_handler));
  }
  else if(expr.id() == ID_AR)
  {
    // AR(f1, f2) = !EU(!f1, !f2)
    auto &AR_expr = to_AR_expr(expr);
    return !EU(
      model,
      !bdd_ctl(model, AR_expr.lhs(), atomic_proposition_bdds, message_handler),
      !bdd_ctl(model, AR_expr.rhs(), atomic_proposition_bdds, message_handler));
  }
  else if(expr.id() == ID_literal)
  {
    auto var_no = to_literal_expr(expr).get_literal().var_no();
    auto it = atomic_proposition_bdds.find(var_no);
    if(it != atomic_proposition_bdds.end())
    {
      if(to_literal_expr(expr).get_literal().sign())
        return !it->second;
      else
        return it->second;
    }
  }

  messaget message(message_handler);
  message.error() << "unsupported property -- `" << expr.id()
                  << "' not implemented" << messaget::eom;
  throw 0;
}

/*******************************************************************\

Function: initial_states

  Inputs:

 Outputs:

 Purpose: conjunction of initial-state and constraint BDDs

\*******************************************************************/

static BDD initial_states(const bdd_modelt &model)
{
  BDD result = model.mgr.True();
  for(const auto &i : model.initial)
    result = result & i;
  for(const auto &c : model.constraints)
    result = result & c;
  return result;
}

/*******************************************************************\

Function: bdd_check_ctl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bdd_check_resultt bdd_check_ctl(
  const bdd_modelt &model,
  const exprt &property,
  const std::map<unsigned, mini_bddt> &atomic_proposition_bdds,
  message_handlert &message_handler)
{
  BDD not_f =
    !bdd_ctl(model, property, atomic_proposition_bdds, message_handler);

  BDD intersection = not_f & initial_states(model);

  bdd_check_resultt result;
  if(intersection.is_false())
    result.status = bdd_check_resultt::statust::PROVED;
  else
    result.status = bdd_check_resultt::statust::REFUTED;
  return result;
}

/*******************************************************************\

Function: bdd_check_AGp

  Inputs:

 Outputs:

 Purpose: backward reachability for AG p

\*******************************************************************/

bdd_check_resultt bdd_check_AGp(
  const bdd_modelt &model,
  const exprt &property,
  const std::map<unsigned, mini_bddt> &atomic_proposition_bdds,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  const exprt &sub_expr = to_unary_expr(property).op();
  BDD p = bdd_ctl(model, sub_expr, atomic_proposition_bdds, message_handler);

  BDD states = !p;
  unsigned iteration = 0;

  for(const auto &c : model.constraints)
    states = states & c;

  while(true)
  {
    iteration++;
    message.statistics() << "Iteration " << iteration << messaget::eom;

    BDD intersection = states & initial_states(model);

    if(!intersection.is_false())
    {
      bdd_check_resultt result;
      result.status = bdd_check_resultt::statust::REFUTED;
      result.number_of_timeframes = iteration;
      return result;
    }

    BDD states_next = current_to_next(model, states);

    BDD conjunction = states_next;
    for(const auto &t : model.transition)
      conjunction = conjunction & t;
    for(const auto &c : model.constraints)
      conjunction = conjunction & c;

    BDD pre_image = project_next(model, conjunction);
    BDD set_union = states | pre_image;

    if((set_union == states).is_true())
    {
      bdd_check_resultt result;
      result.status = bdd_check_resultt::statust::PROVED;
      result.number_of_timeframes = iteration;
      return result;
    }

    states = set_union;
  }
}
