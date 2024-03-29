/*******************************************************************\

Module: Unwinding the Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "property.h"

#include <util/expr_iterator.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

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
  else if(expr.id() == ID_sva_always)
    return true;
  else
    return false;
}

/*******************************************************************\

Function: property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::map<std::size_t, exprt::operandst> property_obligations(
  const exprt &property_expr,
  message_handlert &message_handler,
  decision_proceduret &solver,
  std::size_t no_timeframes,
  const namespacet &ns)
{
  PRECONDITION(no_timeframes > 0);

  std::map<std::size_t, exprt::operandst> obligations;

  messaget message(message_handler);

  // Initial state only property?
  if(
    !is_temporal_operator(property_expr) ||
    property_expr.id() == ID_sva_cycle_delay ||
    property_expr.id() == ID_sva_nexttime ||
    property_expr.id() == ID_sva_s_nexttime)
  {
    exprt tmp = instantiate(property_expr, 0, no_timeframes, ns);
    obligations[0].push_back(solver.handle(tmp));
    return obligations;
  }

  // We want AG p.
  auto &p = [](const exprt &expr) -> const exprt & {
    if(expr.id() == ID_AG)
      return to_AG_expr(expr).op();
    else if(expr.id() == ID_G)
      return to_G_expr(expr).op();
    else if(expr.id() == ID_sva_always)
      return to_sva_always_expr(expr).op();
    else
      PRECONDITION(false);
  }(property_expr);

  for(std::size_t c = 0; c < no_timeframes; c++)
  {
    exprt tmp=
      instantiate(p, c, no_timeframes, ns);

    auto handle = solver.handle(tmp);
    obligations[c].push_back(std::move(handle));
  }

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
  auto obligations = property_obligations(
    property_expr, message_handler, solver, no_timeframes, ns);

  // Map obligations onto timeframes.
  prop_handles.resize(no_timeframes, true_exprt());
  for(auto &obligation_it : obligations)
  {
    auto t = obligation_it.first;
    DATA_INVARIANT(t < no_timeframes, "obligation must have valid timeframe");
    prop_handles[t] = conjunction(obligation_it.second);
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
