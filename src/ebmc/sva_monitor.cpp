/*******************************************************************\

Module: SVA Monitor

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "sva_monitor.h"

#include <util/arith_tools.h>

#include <temporal-logic/ltl.h>
#include <temporal-logic/nnf.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

#include "ebmc_properties.h"
#include "transition_system.h"

class monitor_resultt
{
protected:
  // use the factories below
  monitor_resultt()
  {
  }

public:
  bool is_error() const
  {
    return !_error.empty();
  }

  const std::string &error() const
  {
    PRECONDITION(is_error());
    return _error;
  }

  // factory for the 'error' case
  static monitor_resultt error(std::string __error)
  {
    monitor_resultt monitor_result;
    monitor_result._error = std::move(__error);
    return monitor_result;
  }

  // factory for the 'safe' case
  static monitor_resultt safe(exprt __safe)
  {
    monitor_resultt monitor_result;
    monitor_result._safe = std::move(__safe);
    return monitor_result;
  }

  const exprt &safe() const
  {
    return _safe;
  }

  // factory for the result of a sequence monitor
  static monitor_resultt sequence(exprt __safe, exprt __match_end)
  {
    monitor_resultt monitor_result;
    monitor_result._safe = std::move(__safe);
    monitor_result._match_end = std::move(__match_end);
    return monitor_result;
  }

  // signals the endpoint of a sequence match
  const exprt &match_end() const
  {
    return _match_end;
  }

  exprt as_LTL() const;

protected:
  std::string _error;
  exprt _safe = true_exprt{};
  exprt _liveness = true_exprt{};
  exprt _match_end = false_exprt{};
};

exprt monitor_resultt::as_LTL() const
{
  PRECONDITION(!is_error());

  exprt::operandst conjuncts;

  if(!_safe.is_true())
    conjuncts.push_back(G_exprt{_safe});

  if(!_liveness.is_true())
    conjuncts.push_back(G_exprt{F_exprt{_liveness}});

  return conjunction(conjuncts);
}

static symbol_exprt
aux_symbol(transition_systemt &transition_system, irep_idt base_name)
{
  auxiliary_symbolt symbol{
    "sva-monitor::" + id2string(base_name),
    bool_typet{},
    transition_system.main_symbol->mode};

  symbol.is_state_var = true;
  symbol.module = transition_system.main_symbol->module;
  symbol.base_name = base_name;

  auto result = transition_system.symbol_table.insert(std::move(symbol));
  CHECK_RETURN(result.second);

  return result.first.symbol_expr();
}

static exprt next(symbol_exprt symbol_expr)
{
  exprt tmp = std::move(symbol_expr);
  tmp.id(ID_next_symbol);
  return tmp;
}

/// Recursion for creating a safety automaton for an SVA sequence.
/// * the monitor starts with the given "active" signal, which
///   is expected to stay on once set.
/// * the monitor returns "safe" and "match_end".
monitor_resultt sva_sequence_monitor_rec(
  transition_systemt &transition_system,
  const exprt &active,
  const exprt &sequence_expr)
{
  if(!has_temporal_operator(sequence_expr))
  {
    // A sample -- matches and is safe if true
    auto implication = implies_exprt{active, sequence_expr};
    return monitor_resultt::sequence(implication, implication);
  }
  else if(sequence_expr.id() == ID_sva_sequence_concatenation)
  {
    auto &concatenation = to_sva_sequence_concatenation_expr(sequence_expr);
    auto &lhs = concatenation.lhs();
    auto &rhs = concatenation.rhs();

    // 1. The 'active' signal of the rhs is the 'finish' signal of the lhs.
    // 2. The overall 'safe' signal is the conjunction of lhs/rhs.
    // 3. The overall 'match_end' signal is the rhs match_end signal.
    auto lhs_rec = sva_sequence_monitor_rec(transition_system, active, lhs);
    if(lhs_rec.is_error())
      return lhs_rec;

    auto rhs_rec =
      sva_sequence_monitor_rec(transition_system, lhs_rec.match_end(), rhs);
    if(rhs_rec.is_error())
      return rhs_rec;

    return monitor_resultt::sequence(
      and_exprt{lhs_rec.safe(), rhs_rec.safe()}, rhs_rec.match_end());
  }
  else if(sequence_expr.id() == ID_sva_cycle_delay)
  {
    auto &delay = to_sva_cycle_delay_expr(sequence_expr);

    // Delay the 'active' signal as specified.
    if(delay.to().is_nil())
    {
      //return sva_monitor_rec(transition_system, delayed_active, delay.op());
      return monitor_resultt::error("no support for ##[x]");
    }
    else if(delay.is_unbounded())
    {
      return monitor_resultt::error("no support for ##[x:$]");
    }
    else
    {
      return monitor_resultt::error("no support for ##[x:y]");
    }
  }
  else
    return monitor_resultt::error(
      "no support for " + sequence_expr.id_string());
}

/// Recursion for creating a safety automaton for a safety property.
/// * the property is converted into NNF on the fly.
/// * the monitor starts with the given "active" signal, which
///   is expected to stay on once set.
monitor_resultt sva_property_monitor_rec(
  transition_systemt &transition_system,
  const exprt &active,
  const exprt &property_expr)
{
  if(!has_temporal_operator(property_expr))
  {
    // A state formula only. Needs to hold in "active" states only.
    return monitor_resultt::safe(implies_exprt{active, property_expr});
  }
  else if(property_expr.id() == ID_not)
  {
    // create NNF
    auto &op = to_not_expr(property_expr).op();
    auto nnf_opt = negate_property_node(op);
    if(nnf_opt)
      return sva_property_monitor_rec(transition_system, active, *nnf_opt);
    else
      return monitor_resultt::error("no NNF for " + op.id_string());
  }
  else if(
    property_expr.id() == ID_implies || property_expr.id() == ID_nor ||
    property_expr.id() == ID_nand || property_expr.id() == ID_xor ||
    property_expr.id() == ID_xnor)
  {
    // We rely on NNF.
    return monitor_resultt::error(property_expr.id_string() + " is TBD");
  }
  else if(property_expr.id() == ID_and)
  {
    // The conjunction of safety automata is built by conjoining the
    // 'safe' signal.
    exprt::operandst conjuncts;

    for(auto &op : property_expr.operands())
    {
      auto rec = sva_property_monitor_rec(transition_system, active, op);
      if(rec.is_error())
        return rec;
      conjuncts.push_back(rec.safe());
    }

    return monitor_resultt::safe(conjunction(conjuncts));
  }
  else if(property_expr.id() == ID_or)
  {
    // Build automaton per disjunct.
    // Keep a state bit per automaton to record an unsafe state.
    // Signal an unsafe state when all subautomata signalled an unsafe state.
    return monitor_resultt::error("OR is TBD");
  }
  else if(property_expr.id() == ID_sva_always)
  {
    // Nondeterministically guess when to start monitoring.
    const auto always_activated_expr =
      aux_symbol(transition_system, "always_activated");

    // "always activated" is false in the initial state
    transition_system.trans_expr.init() = and_exprt{
      transition_system.trans_expr.init(), not_exprt{always_activated_expr}};

    const auto always_active_expr =
      aux_symbol(transition_system, "always_active");

    transition_system.trans_expr.trans() = and_exprt{
      transition_system.trans_expr.trans(),
      equal_exprt{next(always_activated_expr), always_active_expr}};

    // once active, always active
    transition_system.trans_expr.invar() = and_exprt{
      transition_system.trans_expr.invar(),
      implies_exprt{always_activated_expr, always_active_expr}};

    // recursion
    auto &op = to_sva_always_expr(property_expr).op();

    return sva_property_monitor_rec(transition_system, always_active_expr, op);
  }
  else if(property_expr.id() == ID_sva_s_always)
  {
    auto &s_always_expr = to_sva_s_always_expr(property_expr);

    if(
      numeric_cast_v<mp_integer>(to_constant_expr(s_always_expr.lower())) ==
        1 &&
      numeric_cast_v<mp_integer>(to_constant_expr(s_always_expr.upper())) == 1)
    {
      // Simply delay "active" one time frame.
      const auto delayed_active_expr =
        aux_symbol(transition_system, "delayed_active");

      transition_system.trans_expr.init() = and_exprt{
        transition_system.trans_expr.init(), not_exprt{delayed_active_expr}};

      transition_system.trans_expr.trans() = and_exprt{
        transition_system.trans_expr.trans(),
        equal_exprt{next(delayed_active_expr), active}};

      return sva_property_monitor_rec(
        transition_system, delayed_active_expr, s_always_expr.op());
    }
    else
      return monitor_resultt::error("s_always is TBD");
  }
  else if(property_expr.id() == ID_sva_sequence_property)
  {
    return sva_sequence_monitor_rec(
      transition_system,
      active,
      to_sva_sequence_property_expr(property_expr).sequence());
  }
  else if(property_expr.id() == ID_sva_weak)
  {
    return sva_sequence_monitor_rec(
      transition_system, active, to_sva_weak_expr(property_expr).sequence());
  }
  else if(property_expr.id() == ID_sva_strong)
  {
    return sva_sequence_monitor_rec(
      transition_system, active, to_sva_strong_expr(property_expr).sequence());
  }
  else
    return monitor_resultt::error(
      "no support for " + property_expr.id_string());
}

exprt sva_monitor_initial(transition_systemt &transition_system)
{
  const auto symbol_expr = aux_symbol(transition_system, "initial");

  // true in the initial state
  transition_system.trans_expr.init() =
    and_exprt{transition_system.trans_expr.init(), symbol_expr};

  // but false in subsequent states
  transition_system.trans_expr.trans() = and_exprt{
    transition_system.trans_expr.trans(), not_exprt{next(symbol_expr)}};

  return symbol_expr;
}

void sva_monitor(
  transition_systemt &transition_system,
  ebmc_propertiest::propertyt &property)
{
  // Create the top-level "start" signal -- on in the initial states exactly.
  auto start = sva_monitor_initial(transition_system);

  // start recursion over property expression
  auto result = sva_property_monitor_rec(
    transition_system, start, property.normalized_expr);

  if(result.is_error())
    property.unsupported(result.error());
  else
    property.normalized_expr = G_exprt{result.safe()};
}

void sva_monitor(
  transition_systemt &transition_system,
  ebmc_propertiest &properties)
{
  for(auto &property : properties.properties)
  {
    sva_monitor(transition_system, property);
  }
}
