/*******************************************************************\

Module: Unwinding the Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "property.h"

#include <util/arith_tools.h>
#include <util/expr_iterator.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <ebmc/ebmc_error.h>
#include <temporal-logic/temporal_expr.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

#include "instantiate_word_level.h"

#include <cstdlib>

/*******************************************************************\

Function: bmc_supports_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmc_supports_property(const exprt &expr)
{
  if(!is_temporal_operator(expr))
  {
    if(!has_temporal_operator(expr))
      return true; // initial state only
    else if(
      expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_implies)
    {
      for(auto &op : expr.operands())
        if(!bmc_supports_property(op))
          return false;
      return true;
    }
    else
      return false;
  }
  else if(expr.id() == ID_sva_cycle_delay)
    return !has_temporal_operator(to_sva_cycle_delay_expr(expr).op());
  else if(expr.id() == ID_sva_nexttime)
    return !has_temporal_operator(to_sva_nexttime_expr(expr).op());
  else if(expr.id() == ID_sva_s_nexttime)
    return !has_temporal_operator(to_sva_s_nexttime_expr(expr).op());
  else if(expr.id() == ID_AG)
    return true;
  else if(expr.id() == ID_G)
    return true;
  else if(expr.id() == ID_AF)
    return true;
  else if(expr.id() == ID_F)
    return true;
  else if(expr.id() == ID_X)
    return bmc_supports_property(to_X_expr(expr).op());
  else if(expr.id() == ID_sva_always)
    return true;
  else if(expr.id() == ID_sva_ranged_always)
    return true;
  else
    return false;
}

/*******************************************************************\

Function: max_property_obligation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void property_obligations_rec(
  const exprt &property_expr,
  decision_proceduret &,
  const mp_integer &current,
  const mp_integer &no_timeframes,
  const namespacet &,
  std::map<mp_integer, exprt::operandst> &obligations);

static std::pair<mp_integer, exprt> max_property_obligation(
  const exprt &property_expr,
  decision_proceduret &solver,
  const mp_integer &current,
  const mp_integer &no_timeframes,
  const namespacet &ns)
{
  // Generate one obligation, equivalent to the conjunction
  // for the maximum timeframe.

  std::map<mp_integer, exprt::operandst> obligations;

  property_obligations_rec(
    property_expr, solver, current, no_timeframes, ns, obligations);

  exprt::operandst conjuncts;
  mp_integer max_timeframe = 0;

  for(auto &[timeframe, exprs] : obligations)
  {
    max_timeframe = std::max(max_timeframe, timeframe);
    for(auto &conjunct : exprs)
      conjuncts.push_back(conjunct);
  }

  return std::pair<mp_integer, exprt>{max_timeframe, conjunction(conjuncts)};
}

/*******************************************************************\

Function: property_obligations_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void property_obligations_rec(
  const exprt &property_expr,
  decision_proceduret &solver,
  const mp_integer &current,
  const mp_integer &no_timeframes,
  const namespacet &ns,
  std::map<mp_integer, exprt::operandst> &obligations)
{
  PRECONDITION(current >= 0 && current < no_timeframes);

  if(property_expr.id() == ID_X)
  {
    auto next = current + 1;
    if(next < no_timeframes)
    {
      auto &op = to_X_expr(property_expr).op();
      property_obligations_rec(
        op, solver, next, no_timeframes, ns, obligations);
    }
  }
  else if(
    property_expr.id() == ID_AG || property_expr.id() == ID_G ||
    property_expr.id() == ID_sva_always)
  {
    // We want AG phi.
    auto &phi = [](const exprt &expr) -> const exprt & {
      if(expr.id() == ID_AG)
        return to_AG_expr(expr).op();
      else if(expr.id() == ID_G)
        return to_G_expr(expr).op();
      else if(expr.id() == ID_sva_always)
        return to_sva_always_expr(expr).op();
      else
        PRECONDITION(false);
    }(property_expr);

    for(mp_integer c = current; c < no_timeframes; ++c)
    {
      property_obligations_rec(phi, solver, c, no_timeframes, ns, obligations);
    }
  }
  else if(
    property_expr.id() == ID_AF || property_expr.id() == ID_F ||
    property_expr.id() == ID_sva_s_eventually)
  {
    const auto &phi = to_unary_expr(property_expr).op();

    // Counterexamples to Fφ must have a loop.
    // We consider l-k loops with l<k.
    for(mp_integer k = current + 1; k < no_timeframes; ++k)
    {
      // The following needs to be satisfied for a counterexample
      // to Fφ that loops back in timeframe k:
      //
      // (1) There is a loop from timeframe k back to
      //     some earlier state l with current<=l<k.
      // (2) No state j with current<=j<=k to the end of the
      //     lasso satisfies 'φ'.
      for(mp_integer l = current; l < k; ++l)
      {
        exprt::operandst disjuncts = {not_exprt(lasso_symbol(l, k))};

        for(mp_integer j = current; j <= k; ++j)
        {
          exprt tmp = instantiate(phi, j, no_timeframes, ns);
          disjuncts.push_back(std::move(tmp));
        }

        obligations[k].push_back(disjunction(disjuncts));
      }
    }
  }
  else if(
    property_expr.id() == ID_sva_ranged_always ||
    property_expr.id() == ID_sva_s_always)
  {
    auto &phi = property_expr.id() == ID_sva_ranged_always
                  ? to_sva_ranged_always_expr(property_expr).op()
                  : to_sva_s_always_expr(property_expr).op();
    auto &lower = property_expr.id() == ID_sva_ranged_always
                    ? to_sva_ranged_always_expr(property_expr).lower()
                    : to_sva_s_always_expr(property_expr).lower();
    auto &upper = property_expr.id() == ID_sva_ranged_always
                    ? to_sva_ranged_always_expr(property_expr).upper()
                    : to_sva_s_always_expr(property_expr).upper();

    auto from_opt = numeric_cast<mp_integer>(lower);
    if(!from_opt.has_value())
      throw ebmc_errort() << "failed to convert SVA always from index";

    auto from = std::max(mp_integer{0}, *from_opt);

    mp_integer to;

    if(upper.id() == ID_infinity)
    {
      to = no_timeframes - 1;
    }
    else
    {
      auto to_opt = numeric_cast<mp_integer>(upper);
      if(!to_opt.has_value())
        throw ebmc_errort() << "failed to convert SVA always to index";
      to = std::min(*to_opt, no_timeframes - 1);
    }

    for(mp_integer c = from; c <= to; ++c)
    {
      property_obligations_rec(phi, solver, c, no_timeframes, ns, obligations);
    }
  }
  else if(property_expr.id() == ID_and)
  {
    // generate seperate obligations for each conjunct
    for(auto &op : to_and_expr(property_expr).operands())
      property_obligations_rec(
        op, solver, current, no_timeframes, ns, obligations);
  }
  else if(property_expr.id() == ID_or)
  {
    // generate one obligation, equivalent to the disjunction,
    // for the maximum timeframe
    mp_integer max_timeframe = 0;
    exprt::operandst disjuncts;

    for(auto &op : to_or_expr(property_expr).operands())
    {
      auto obligation =
        max_property_obligation(op, solver, current, no_timeframes, ns);
      max_timeframe = std::max(max_timeframe, obligation.first);
      disjuncts.push_back(obligation.second);
    }

    obligations[max_timeframe].push_back(disjunction(disjuncts));
  }
  else
  {
    // current state property
    exprt tmp = instantiate(property_expr, current, no_timeframes, ns);
    obligations[current].push_back(tmp);
  }
}

/*******************************************************************\

Function: property_obligations

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::map<mp_integer, exprt::operandst> property_obligations(
  const exprt &property_expr,
  decision_proceduret &solver,
  const mp_integer &no_timeframes,
  const namespacet &ns)
{
  std::map<mp_integer, exprt::operandst> obligations;

  property_obligations_rec(
    property_expr, solver, 0, no_timeframes, ns, obligations);

  return obligations;
}

/*******************************************************************\

Function: property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void property(
  const exprt &property_expr,
  exprt::operandst &prop_handles,
  message_handlert &message_handler,
  decision_proceduret &solver,
  std::size_t no_timeframes,
  const namespacet &ns)
{
  // The first element of the pair is the length of the
  // counterexample, and the second is the condition that
  // must be valid for the property to hold.
  auto obligations =
    property_obligations(property_expr, solver, no_timeframes, ns);

  // Map obligations onto timeframes.
  prop_handles.resize(no_timeframes, true_exprt());
  for(auto &obligation_it : obligations)
  {
    auto t = obligation_it.first;
    DATA_INVARIANT(
      t >= 0 && t < no_timeframes, "obligation must have valid timeframe");
    auto t_int = numeric_cast_v<std::size_t>(t);
    prop_handles[t_int] = solver.handle(conjunction(obligation_it.second));
  }
}

/*******************************************************************\

Function: states_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt states_equal(
  const mp_integer &k,
  const mp_integer &i,
  const std::vector<symbol_exprt> &variables_to_compare)
{
  // We require k<i to avoid the symmetric constraints.
  PRECONDITION(k < i);

  exprt::operandst conjuncts;
  conjuncts.reserve(variables_to_compare.size());

  for(auto &var : variables_to_compare)
  {
    auto i_var = timeframe_symbol(i, var);
    auto k_var = timeframe_symbol(k, var);
    conjuncts.push_back(equal_exprt(i_var, k_var));
  }

  return conjunction(std::move(conjuncts));
}

/*******************************************************************\

Function: lasso_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt lasso_symbol(const mp_integer &k, const mp_integer &i)
{
  // True when states i and k are equal.
  // We require k<i to avoid the symmetric constraints.
  PRECONDITION(k < i);
  irep_idt lasso_identifier =
    "lasso::" + integer2string(i) + "-back-to-" + integer2string(k);
  return symbol_exprt(lasso_identifier, bool_typet());
}

/*******************************************************************\

Function: lasso_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void lasso_constraints(
  decision_proceduret &solver,
  const mp_integer &no_timeframes,
  const namespacet &ns,
  const irep_idt &module_identifier)
{
  // The definition of a lasso to state s_i is that there
  // is an identical state s_k = s_i with k<i.
  // "Identical" is defined as "state variables and top-level inputs match".

  std::vector<symbol_exprt> variables_to_compare;

  // Gather the state variables.
  const symbol_tablet &symbol_table = ns.get_symbol_table();
  auto lower = symbol_table.symbol_module_map.lower_bound(module_identifier);
  auto upper = symbol_table.symbol_module_map.upper_bound(module_identifier);

  for(auto it = lower; it != upper; it++)
  {
    const symbolt &symbol = ns.lookup(it->second);

    if(symbol.is_state_var)
      variables_to_compare.push_back(symbol.symbol_expr());
  }

  // gather the top-level inputs
  const auto &module_symbol = ns.lookup(module_identifier);
  DATA_INVARIANT(module_symbol.type.id() == ID_module, "expected a module");
  const auto &ports = module_symbol.type.find(ID_ports);

  for(auto &port : static_cast<const exprt &>(ports).operands())
  {
    DATA_INVARIANT(port.id() == ID_symbol, "port must be a symbol");
    if(port.get_bool(ID_input) && !port.get_bool(ID_output))
    {
      symbol_exprt input_symbol(port.get(ID_identifier), port.type());
      input_symbol.add_source_location() = port.source_location();
      variables_to_compare.push_back(std::move(input_symbol));
    }
  }

  for(mp_integer i = 1; i < no_timeframes; ++i)
  {
    for(mp_integer k = 0; k < i; ++k)
    {
      // Is there a loop back from time frame i back to time frame k?
      auto lasso_symbol = ::lasso_symbol(k, i);
      auto equal = states_equal(k, i, variables_to_compare);
      solver.set_to_true(equal_exprt(lasso_symbol, equal));
    }
  }
}

/*******************************************************************\

Function: requires_lasso_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool requires_lasso_constraints(const exprt &expr)
{
  for(auto subexpr_it = expr.depth_cbegin(), subexpr_end = expr.depth_cend();
      subexpr_it != subexpr_end;
      subexpr_it++)
  {
    if(
      subexpr_it->id() == ID_sva_until || subexpr_it->id() == ID_sva_s_until ||
      subexpr_it->id() == ID_sva_eventually ||
      subexpr_it->id() == ID_sva_s_eventually || subexpr_it->id() == ID_AF ||
      subexpr_it->id() == ID_F)
    {
      return true;
    }
  }

  return false;
}
