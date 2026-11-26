/*******************************************************************\

Module: $past Instrumentation

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "instrument_past.h"

#include <util/arith_tools.h>
#include <util/expr_identity_map.h>
#include <util/replace_expr.h>

#include <verilog/verilog_expr.h>

#include "ebmc_error.h"

#include <set>
#include <unordered_set>
#include <utility>
#include <vector>

// The set is ordered to get a stable numbering
using past_sett = std::set<verilog_past_exprt>;

// The expressions are DAGs with much sharing. Each distinct node is
// visited once; a walk of the tree would take time exponential in the
// depth of the expression.
void collect_past(const exprt &expr, past_sett &past_set)
{
  std::unordered_set<const void *> visited;
  std::vector<const exprt *> stack{&expr};

  while(!stack.empty())
  {
    const exprt &e = *stack.back();
    stack.pop_back();

    if(!visited.insert(&e.read()).second)
      continue;

    if(e.id() == ID_verilog_past)
      past_set.insert(to_verilog_past_expr(e));

    for(auto &op : e.operands())
      stack.push_back(&op);
  }
}

void collect_past(
  const transition_systemt &transition_system,
  past_sett &past_set)
{
  collect_past(transition_system.trans_expr, past_set);
}

void collect_past(const ebmc_propertiest &properties, past_sett &past_set)
{
  for(auto &property : properties.properties)
  {
    collect_past(property.normalized_expr, past_set);
  }
}

/// Adds missing $past(x, y) when $past(x, z) with z>y exists.
void complete_past_set(past_sett &past_set)
{
  past_sett new_entries;

  for(const auto &past_expr : past_set)
  {
    auto ticks_int_opt = numeric_cast<mp_integer>(past_expr.ticks());
    if(!ticks_int_opt.has_value())
      throw ebmc_errort() << "$past with non-constant number of ticks";

    for(mp_integer i = 1; i < *ticks_int_opt; ++i)
    {
      auto new_past_expr = past_expr;
      new_past_expr.ticks() = from_integer(i, new_past_expr.ticks().type());
      new_entries.insert(new_past_expr);
    }
  }

  // now merge in the new entries
  past_set.insert(new_entries.begin(), new_entries.end());
}

replace_mapt
model_past(const past_sett &past_set, transition_systemt &transition_system)
{
  replace_mapt past_map;
  std::size_t number = 0;

  for(auto &past_expr : past_set)
  {
    auto ticks_int_opt = numeric_cast<mp_integer>(past_expr.ticks());
    if(!ticks_int_opt.has_value())
      throw ebmc_errort() << "$past with non-constant number of ticks";

    if(*ticks_int_opt == 0)
    {
      past_map[past_expr] = past_expr.what();
    }
    else if(*ticks_int_opt >= 1)
    {
      // construct a fresh symbol
      number++;
      const irep_idt identifier = "ebmc::$past" + std::to_string(number) + "@" +
                                  integer2string(*ticks_int_opt);
      const symbol_exprt symbol_expr(identifier, past_expr.type());

      // add to symbol table
      {
        symbolt symbol{
          identifier, past_expr.type(), transition_system.main_symbol->mode};
        symbol.is_state_var = true;
        symbol.module = transition_system.main_symbol->module;
        transition_system.symbol_table.add(std::move(symbol));
      }

      past_map[past_expr] = symbol_expr;
    }
  }

  // Now generate constraints
  exprt::operandst init_conjuncts;

  for(auto &past_expr : past_set)
  {
    auto ticks_int_opt = numeric_cast<mp_integer>(past_expr.ticks());
    if(!ticks_int_opt.has_value())
      throw ebmc_errort() << "$past with non-constant number of ticks";

    if(*ticks_int_opt >= 1)
    {
      auto symbol_expr = past_map[past_expr];

      // These start with zero
      init_conjuncts.push_back(
        equal_exprt{symbol_expr, past_expr.default_value()});
    }
  }

  if(!init_conjuncts.empty())
    transition_system.trans_expr.init() = and_exprt{
      transition_system.trans_expr.init(), conjunction(init_conjuncts)};

  exprt::operandst trans_conjuncts;

  for(auto &past_expr : past_set)
  {
    auto ticks_int_opt = numeric_cast<mp_integer>(past_expr.ticks());
    if(!ticks_int_opt.has_value())
      throw ebmc_errort() << "$past with non-constant number of ticks";

    if(*ticks_int_opt >= 1)
    {
      auto symbol_expr = past_map[past_expr];

      exprt next_symbol_expr = to_symbol_expr(symbol_expr);
      next_symbol_expr.id(ID_next_symbol);

      exprt rhs;

      if(*ticks_int_opt == 1)
        rhs = past_expr.what();
      else
      {
        auto new_past_expr = past_expr;
        new_past_expr.ticks() =
          from_integer(*ticks_int_opt - 1, new_past_expr.ticks().type());
        // Must be in map, guaranteed by complete_past_set
        auto map_entry = past_map.find(new_past_expr);
        CHECK_RETURN(map_entry != past_map.end());
        rhs = map_entry->second;
      }

      trans_conjuncts.push_back(equal_exprt{next_symbol_expr, rhs});
    }
  }

  if(!trans_conjuncts.empty())
    transition_system.trans_expr.trans() = and_exprt{
      transition_system.trans_expr.trans(), conjunction(trans_conjuncts)};

  return past_map;
}

using replace_past_cachet = expr_identity_mapt<exprt>;

/// Replaces the $past expressions in \p expr by their model. This is
/// done once per distinct node, and nodes without $past are kept as they
/// are, so that the sharing of the expression is preserved.
static exprt replace_past(
  const replace_mapt &past_map,
  const exprt &expr,
  replace_past_cachet &cache)
{
  if(auto cached = cache.find(expr))
    return *cached;

  exprt result = expr;

  auto map_entry =
    expr.id() == ID_verilog_past ? past_map.find(expr) : past_map.end();

  if(map_entry != past_map.end())
    result = map_entry->second;
  else
  {
    for(std::size_t i = 0; i < expr.operands().size(); i++)
    {
      const exprt &op = expr.operands()[i];
      auto new_op = replace_past(past_map, op, cache);
      if(&new_op.read() != &op.read())
        result.operands()[i] = std::move(new_op);
    }
  }

  cache.insert(expr, result);
  return result;
}

static void replace_past(
  const replace_mapt &past_map,
  exprt &expr,
  replace_past_cachet &cache)
{
  expr = replace_past(past_map, std::as_const(expr), cache);
}

void instrument_past_model(
  const replace_mapt &past_map,
  transition_systemt &transition_system)
{
  if(past_map.empty())
    return;

  replace_past_cachet cache;
  replace_past(past_map, transition_system.trans_expr, cache);
}

void instrument_past_model(
  const replace_mapt &past_map,
  ebmc_propertiest &properties)
{
  if(past_map.empty())
    return;

  replace_past_cachet cache;

  for(auto &property : properties.properties)
    replace_past(past_map, property.normalized_expr, cache);
}

void instrument_past(
  transition_systemt &transition_system,
  ebmc_propertiest &properties)
{
  past_sett past_set;
  collect_past(transition_system, past_set);
  collect_past(properties, past_set);

  complete_past_set(past_set);

  auto past_map = model_past(past_set, transition_system);

  instrument_past_model(past_map, transition_system);
  instrument_past_model(past_map, properties);
}

bool has_past(
  const transition_systemt &transition_system,
  const ebmc_propertiest &properties)
{
  past_sett past_set;
  collect_past(transition_system, past_set);
  collect_past(properties, past_set);

  return !past_set.empty();
}
