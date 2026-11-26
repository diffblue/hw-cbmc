/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "instantiate_word_level.h"

#include <util/ebmc_util.h>
#include <util/expr_util.h>

#include <ebmc/ebmc_error.h>
#include <temporal-logic/temporal_expr.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>
#include <verilog/verilog_expr.h>

#include "sequence.h"

#include <map>
#include <memory>
#include <optional>
#include <unordered_map>

/*******************************************************************\

Function: timeframe_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string
timeframe_identifier(const mp_integer &timeframe, const irep_idt &identifier)
{
  return id2string(identifier) + "@" + integer2string(timeframe);
}

/*******************************************************************\

Function: timeframe_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt timeframe_symbol(const mp_integer &timeframe, symbol_exprt src)
{
  auto result = std::move(src);
  result.identifier(timeframe_identifier(timeframe, result.identifier()));
  return result;
}

/*******************************************************************\

   Class: wl_instantiatet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class wl_instantiatet
{
public:
  wl_instantiatet(
    const mp_integer &_t,
    const mp_integer &_no_timeframes,
    bool _next_symbol_allowed)
    : t(_t),
      no_timeframes(_no_timeframes),
      next_symbol_allowed(_next_symbol_allowed),
      suffix('@' + integer2string(_t))
  {
  }

  /// Instantiate the given expression for timeframe t
  [[nodiscard]] exprt operator()(const exprt &expr)
  {
    return instantiate_rec(expr);
  }

protected:
  const mp_integer t;
  const mp_integer &no_timeframes;
  bool next_symbol_allowed;

  // "@t" and "@(t+1)", computed once
  const std::string suffix;
  std::optional<std::string> next_suffix;

  // Instances of symbols and of next_symbols, keyed by identifier.
  // The first component is the original expression, the second its
  // instance. Occurrences of identical symbols then share one instance,
  // and the identifier is built only once.
  using symbol_cachet = std::unordered_map<irep_idt, std::pair<exprt, exprt>>;
  symbol_cachet symbol_cache, next_symbol_cache;

  // Instances of shared subexpressions, keyed by the node of the
  // original expression, to retain sharing and avoid repeated work.
  // The original expression outlives this object.
  std::unordered_map<const void *, exprt> shared_cache;

  // instantiators for $past
  std::map<mp_integer, std::unique_ptr<wl_instantiatet>> other_timeframes;

  wl_instantiatet &other_timeframe(const mp_integer &u)
  {
    auto &entry = other_timeframes[u];
    if(!entry)
    {
      entry = std::make_unique<wl_instantiatet>(
        u, no_timeframes, next_symbol_allowed);
    }
    return *entry;
  }

  [[nodiscard]] exprt instantiate_symbol(
    const exprt &,
    symbol_cachet &,
    const std::string &timeframe_suffix);
  [[nodiscard]] exprt instantiate_rec(const exprt &);
  [[nodiscard]] exprt instantiate_rec_uncached(const exprt &);
};

/*******************************************************************\

Function: wl_instantiatet::instantiate_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt wl_instantiatet::instantiate_rec(const exprt &expr)
{
  // Only nodes that are referenced more than once can be reached
  // again, so only these are worth caching.
  if(expr.has_operands() && expr.read().ref_count > 1)
  {
    auto entry = shared_cache.find(&expr.read());
    if(entry != shared_cache.end())
      return entry->second;
    auto result = instantiate_rec_uncached(expr);
    shared_cache.emplace(&expr.read(), result);
    return result;
  }
  else
    return instantiate_rec_uncached(expr);
}

/*******************************************************************\

Function: wl_instantiatet::instantiate_symbol

  Inputs:

 Outputs:

 Purpose: Instantiate a symbol or next_symbol in the given timeframe

\*******************************************************************/

exprt wl_instantiatet::instantiate_symbol(
  const exprt &expr,
  symbol_cachet &cache,
  const std::string &timeframe_suffix)
{
  const irep_idt &identifier = expr.get(ID_identifier);
  auto entry = cache.find(identifier);

  // The cached instance is used only when the symbol is identical,
  // including its type and comments.
  if(entry != cache.end())
  {
    const auto &original = entry->second.first;
    if(&original.read() == &expr.read() || original.full_eq(expr))
      return entry->second.second;
  }

  const auto &id_string = id2string(identifier);
  std::string new_identifier;
  new_identifier.reserve(id_string.size() + timeframe_suffix.size());
  new_identifier += id_string;
  new_identifier += timeframe_suffix;

  exprt result = expr;
  result.id(ID_symbol);
  result.set(ID_identifier, new_identifier);

  if(entry == cache.end())
    cache.emplace(identifier, std::make_pair(expr, result));

  return result;
}

/*******************************************************************\

Function: wl_instantiatet::instantiate_rec_uncached

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt wl_instantiatet::instantiate_rec_uncached(const exprt &expr)
{
  // Types are not instantiated.

  if(expr.id() == ID_next_symbol)
  {
    PRECONDITION(next_symbol_allowed);
    if(!next_suffix.has_value())
      next_suffix = '@' + integer2string(t + 1);
    return instantiate_symbol(expr, next_symbol_cache, *next_suffix);
  }
  else if(expr.id() == ID_symbol)
  {
    return instantiate_symbol(expr, symbol_cache, suffix);
  }
  else if(expr.id() == ID_nondet_symbol)
  {
    // A non-deterministic choice is made anew in every time frame. The
    // identifier of a nondet_symbol may be that of a symbol, e.g., of the
    // wire whose bits it gives; the prefix keeps it distinct from the
    // symbol in the same time frame.
    exprt result = expr;
    auto identifier = expr.get(ID_identifier);
    result.set(ID_identifier, "nondet::" + id2string(identifier) + suffix);
    return result;
  }
  else if(
    expr.id() == ID_typecast && expr.type().id() == ID_bool &&
    to_typecast_expr(expr).op().type().id() == ID_verilog_sva_sequence)
  {
    // should have been done by property_obligations_rec
    PRECONDITION(false);
  }
  else if(
    expr.id() == ID_sva_sequence_property || expr.id() == ID_sva_weak ||
    expr.id() == ID_sva_strong)
  {
    // should have been done by property_obligations_rec
    PRECONDITION(false);
  }
  else if(expr.id() == ID_verilog_past)
  {
    auto &verilog_past = to_verilog_past_expr(expr);

    mp_integer ticks;
    if(to_integer_non_constant(verilog_past.ticks(), ticks))
      throw "failed to convert $past number of ticks";

    if(ticks > t)
    {
      // return the 'default value' for the type
      return verilog_past.default_value();
    }
    else
    {
      return other_timeframe(t - ticks).instantiate_rec(verilog_past.what());
    }
  }
  else if(is_temporal_operator(expr))
  {
    // should have been done by property_obligations_rec
    throw ebmc_errort() << "instantiate_word_level got temporal operator "
                        << expr.id();
  }
  else
  {
    // The result shares the node of the original expression unless an
    // operand changes. The new operands are collected before any copy
    // of the node is made, since a copy would raise the reference
    // counts of the original operands, which instantiate_rec uses to
    // decide what to cache.
    const auto &operands = expr.operands();
    exprt::operandst new_operands;

    for(std::size_t i = 0; i < operands.size(); i++)
    {
      exprt op = instantiate_rec(operands[i]);

      if(!new_operands.empty())
        new_operands.push_back(std::move(op));
      else if(&op.read() != &operands[i].read())
      {
        new_operands.reserve(operands.size());
        new_operands.insert(
          new_operands.end(), operands.begin(), operands.begin() + i);
        new_operands.push_back(std::move(op));
      }
    }

    if(new_operands.empty())
      return expr;

    // Build a new node rather than copying the original one, which
    // would copy the operands.
    exprt result{expr.id()};
    result.get_named_sub() = expr.get_named_sub();
    result.operands().swap(new_operands);
    return result;
  }
}

/*******************************************************************\

Function: instantiate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt instantiate(
  const exprt &expr,
  const mp_integer &t,
  const mp_integer &no_timeframes)
{
  wl_instantiatet wl_instantiate(t, no_timeframes, true);
  return wl_instantiate(expr);
}

/*******************************************************************\

Function: instantiate_state_predicate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt instantiate_state_predicate(
  const exprt &expr,
  const mp_integer &current,
  const mp_integer &no_timeframes)
{
  PRECONDITION(expr.type().id() == ID_bool);
  wl_instantiatet wl_instantiate(current, no_timeframes, false);
  return wl_instantiate(expr);
}
