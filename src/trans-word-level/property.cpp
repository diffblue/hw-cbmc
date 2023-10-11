/*******************************************************************\

Module: Unwinding the Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "property.h"

#include <util/expr_iterator.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include "instantiate_word_level.h"

#include <cstdlib>

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
  messaget message(message_handler);

  if(property_expr.is_true())
  {
    prop_handles.resize(no_timeframes, true_exprt());
    return;
  }

  if(property_expr.id()!=ID_AG &&
     property_expr.id()!=ID_sva_always)
  {
    message.error() << "unsupported property - only SVA always implemented"
                    << messaget::eom;
    exit(1);
  }

  const exprt &p = to_unary_expr(property_expr).op();

  for(std::size_t c = 0; c < no_timeframes; c++)
  {
    exprt tmp=
      instantiate(p, c, no_timeframes, ns);

    auto handle = solver.handle(tmp);
    prop_handles.push_back(std::move(handle));
  }
}

/*******************************************************************\

Function: states_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt states_equal(
  std::size_t i,
  std::size_t k,
  const std::vector<symbol_exprt> &state_vars)
{
  exprt::operandst conjuncts;
  conjuncts.reserve(state_vars.size());

  for(auto &var : state_vars)
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

symbol_exprt lasso_symbol(std::size_t timeframe)
{
  irep_idt lasso_identifier = "lasso::" + std::to_string(timeframe);
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
  std::size_t no_timeframes,
  const namespacet &ns,
  const irep_idt &module_identifier)
{
  // gather the state variables
  std::vector<symbol_exprt> state_vars;
  const symbol_tablet &symbol_table = ns.get_symbol_table();

  auto lower = symbol_table.symbol_module_map.lower_bound(module_identifier);
  auto upper = symbol_table.symbol_module_map.upper_bound(module_identifier);

  for(auto it = lower; it != upper; it++)
  {
    const symbolt &symbol = ns.lookup(it->second);

    if(symbol.is_state_var)
      state_vars.push_back(symbol.symbol_expr());
  }

  for(std::size_t i = 1; i < no_timeframes; i++)
  {
    // Is there a loop back to any time frame k with k<i?
    exprt::operandst disjuncts;
    disjuncts.reserve(i);

    for(std::size_t k = 0; k < i; k++)
      disjuncts.push_back(states_equal(k, i, state_vars));

    auto lasso_symbol = ::lasso_symbol(i);
    solver.set_to_true(equal_exprt(lasso_symbol, disjunction(disjuncts)));
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
      subexpr_it->id() == ID_sva_s_eventually)
    {
      return true;
    }
  }

  return false;
}
