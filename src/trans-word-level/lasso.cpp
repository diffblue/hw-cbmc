/*******************************************************************\

Module: Lasso Constraints

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "lasso.h"

#include <util/expr_iterator.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include "instantiate_word_level.h"

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

#define LASSO_PREFIX "lasso::"

symbol_exprt lasso_symbol(const mp_integer &k, const mp_integer &i)
{
  // True when states i and k are equal.
  // We require k<i to avoid the symmetric constraints.
  PRECONDITION(k < i);
  irep_idt lasso_identifier =
    LASSO_PREFIX + integer2string(i) + "-back-to-" + integer2string(k);
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

Function: uses_lasso_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool uses_lasso_symbol(const exprt &expr)
{
  for(auto subexpr_it = expr.depth_cbegin(), subexpr_end = expr.depth_cend();
      subexpr_it != subexpr_end;
      subexpr_it++)
  {
    if(subexpr_it->id() == ID_symbol)
      if(to_symbol_expr(*subexpr_it).get_identifier().starts_with(LASSO_PREFIX))
      {
        return true;
      }
  }

  return false;
}

/*******************************************************************\

Function: uses_lasso_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool uses_lasso_symbol(const exprt::operandst &exprs)
{
  for(auto &expr : exprs)
    if(::uses_lasso_symbol(expr))
      return true;
  return false;
}
