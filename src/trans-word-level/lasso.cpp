/*******************************************************************\

Module: Lasso Constraints

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "lasso.h"

#include <util/irep_hash.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include "instantiate_word_level.h"

#include <unordered_map>
#include <unordered_set>
#include <vector>

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

Function: lasso_select_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#define LASSO_SELECT_PREFIX LASSO_PREFIX "select-"

symbol_exprt lasso_select_symbol(const mp_integer &j, const mp_integer &last)
{
  PRECONDITION(j < last);
  irep_idt identifier = LASSO_SELECT_PREFIX + integer2string(last) +
                        "-back-to-" + integer2string(j);
  return symbol_exprt(identifier, bool_typet());
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
  const irep_idt &module_identifier,
  const std::set<irep_idt> &used_lasso_symbols,
  const std::optional<std::set<irep_idt>> &relevant_variables)
{
  // The definition of a lasso to state s_i is that there
  // is an identical state s_k = s_i with k<i.
  // "Identical" is defined as "state variables and top-level inputs match".
  // Variables that are not relevant, i.e., that are neither read by the
  // transition system nor by the properties, are not compared.

  std::vector<symbol_exprt> variables_to_compare;

  // Gather the state variables, and the inputs.
  const symbol_tablet &symbol_table = ns.get_symbol_table();
  auto lower = symbol_table.symbol_module_map.lower_bound(module_identifier);
  auto upper = symbol_table.symbol_module_map.upper_bound(module_identifier);

  for(auto it = lower; it != upper; it++)
  {
    const symbolt &symbol = ns.lookup(it->second);

    if(
      (symbol.is_state_var || symbol.is_input) &&
      (!relevant_variables.has_value() ||
       relevant_variables->find(symbol.name) != relevant_variables->end()))
    {
      variables_to_compare.push_back(symbol.symbol_expr());
    }
  }

  // We sort the set of variables to compare,
  // to get a deterministic formula
  auto ordering = [](const symbol_exprt &a, const symbol_exprt &b)
  { return id2string(a.identifier()) < id2string(b.identifier()); };

  std::sort(variables_to_compare.begin(), variables_to_compare.end(), ordering);

  bool selectors_used = false;
  bool pairs_used = false;

  for(auto &identifier : used_lasso_symbols)
  {
    if(identifier.starts_with(LASSO_SELECT_PREFIX))
      selectors_used = true;
    else
      pairs_used = true;
  }

  const mp_integer last = no_timeframes - 1;

  // Create the constraints for the pairs of states.
  // The linear encoding only needs the pairs that end in the last
  // timeframe.
  if(pairs_used || selectors_used)
  {
    for(mp_integer i = pairs_used ? 1 : last; i < no_timeframes; ++i)
    {
      for(mp_integer k = 0; k < i; ++k)
      {
        // Is there a loop back from time frame i back to time frame k?
        auto lasso_symbol = ::lasso_symbol(k, i);

        if(
          (selectors_used && i == last) ||
          used_lasso_symbols.find(lasso_symbol.identifier()) !=
            used_lasso_symbols.end())
        {
          auto equal = states_equal(k, i, variables_to_compare);
          solver.set_to_true(equal_exprt(lasso_symbol, equal));
        }
      }
    }
  }

  // The loop selectors of the linear encoding.
  // A selector may only be true when the states are equal,
  // and at most one selector is true.
  if(selectors_used)
  {
    exprt selected_so_far = false_exprt{};

    for(mp_integer j = 0; j < last; ++j)
    {
      auto select = lasso_select_symbol(j, last);
      solver.set_to_true(implies_exprt{select, lasso_symbol(j, last)});

      if(j != 0)
        solver.set_to_true(not_exprt{and_exprt{selected_so_far, select}});

      if(j + 1 < last)
        selected_so_far = solver.handle(or_exprt{selected_so_far, select});
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
  // The BMC obligations share subexpressions heavily (e.g., the
  // disjunctions built for until/release), hence visit every shared
  // node only once instead of walking the tree.
  std::unordered_set<const void *> visited;
  std::vector<const exprt *> stack{&expr};

  while(!stack.empty())
  {
    const exprt &e = *stack.back();
    stack.pop_back();

    if(!visited.insert(&e.read()).second)
      continue;

    if(e.id() == ID_symbol)
    {
      if(to_symbol_expr(e).identifier().starts_with(LASSO_PREFIX))
        return true;
    }

    for(auto &op : e.operands())
      stack.push_back(&op);
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

/*******************************************************************\

Function: collect_lasso_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void collect_lasso_symbols(
  const exprt::operandst &exprs,
  std::set<irep_idt> &dest)
{
  // The obligations share subexpressions; visit each shared node once.
  std::unordered_set<const void *> visited;

  for(auto &expr : exprs)
  {
    std::vector<const exprt *> stack{&expr};

    while(!stack.empty())
    {
      const exprt &e = *stack.back();
      stack.pop_back();

      if(!visited.insert(&e.read()).second)
        continue;

      if(e.id() == ID_symbol)
      {
        auto &identifier = to_symbol_expr(e).identifier();
        if(identifier.starts_with(LASSO_PREFIX))
          dest.insert(identifier);
      }

      for(auto &op : e.operands())
        stack.push_back(&op);
    }
  }
}

/*******************************************************************\

Function: shorten_lasso_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void shorten_lasso_trace(
  trans_tracet &trace,
  const decision_proceduret &solver,
  std::size_t no_timeframes)
{
  if(no_timeframes < 2 || trace.states.size() != no_timeframes)
    return;

  const std::size_t k = no_timeframes - 1;

  // The property must fail in the last timeframe only.
  for(std::size_t t = 0; t < k; t++)
    if(trace.states[t].property_failed)
      return;

  if(!trace.states[k].property_failed)
    return;

  // Which loop was selected?
  std::optional<std::size_t> j_opt;

  for(std::size_t j = 0; j < k; j++)
  {
    if(solver.get(lasso_select_symbol(j, k)).is_true())
    {
      j_opt = j;
      break;
    }
  }

  if(!j_opt.has_value())
    return;

  const std::size_t j = *j_opt;

  // The infinite path is s_0 ... s_k s_{j+1} ... s_k s_{j+1} ...
  // Number the distinct states in the trace.
  struct hasht
  {
    std::size_t operator()(const std::vector<exprt> &values) const
    {
      std::size_t result = 0;
      for(auto &value : values)
        result = hash_combine(result, irep_hash{}(value));
      return result;
    }
  };

  std::unordered_map<std::vector<exprt>, std::size_t, hasht> state_numbers;
  std::vector<std::size_t> number;
  number.reserve(no_timeframes);

  for(auto &state : trace.states)
  {
    std::vector<exprt> values;
    values.reserve(state.assignments.size());
    for(auto &assignment : state.assignments)
      values.push_back(assignment.rhs);
    auto it = state_numbers.emplace(std::move(values), state_numbers.size());
    number.push_back(it.first->second);
  }

  const std::size_t period = k - j;

  auto position = [&](std::size_t t) -> std::size_t
  { return t <= k ? number[t] : number[j + 1 + (t - k - 1) % period]; };

  // Is the suffix of the path from position a equal to the suffix from
  // position b? Once both positions are in the loop, a further 'period'
  // positions suffice.
  auto suffix_equal = [&](std::size_t a, std::size_t b)
  {
    for(std::size_t t = 0; t <= j + 1 + period; t++)
      if(position(a + t) != position(b + t))
        return false;
    return true;
  };

  for(std::size_t end = 1; end <= k; end++)
  {
    for(std::size_t start = 0; start < end; start++)
    {
      if(number[start] == number[end] && suffix_equal(start, end))
      {
        trace.states[k].property_failed = false;
        trace.states[end].property_failed = true;
        return;
      }
    }
  }
}
