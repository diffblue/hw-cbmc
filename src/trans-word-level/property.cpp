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

  if(
    property_expr.id() != ID_AG && property_expr.id() != ID_G &&
    property_expr.id() != ID_sva_always)
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
  std::size_t k,
  std::size_t i,
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

symbol_exprt lasso_symbol(std::size_t k, std::size_t i)
{
  // True when states i and k are equal.
  // We require k<i to avoid the symmetric constraints.
  PRECONDITION(k < i);
  irep_idt lasso_identifier =
    "lasso::" + std::to_string(i) + "-back-to-" + std::to_string(k);
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

  for(std::size_t i = 1; i < no_timeframes; i++)
  {
    for(std::size_t k = 0; k < i; k++)
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
