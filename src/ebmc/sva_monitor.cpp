/*******************************************************************\

Module: SVA Monitor

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "sva_monitor.h"

#include <temporal-logic/ltl.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

#include "ebmc_properties.h"
#include "transition_system.h"

struct monitor_resultt
{
  explicit monitor_resultt(exprt _safety) : safety(std::move(_safety))
  {
  }

  exprt safety = true_exprt{};
  exprt liveness = true_exprt{};
  exprt as_LTL() const;
};

exprt monitor_resultt::as_LTL() const
{
  exprt::operandst conjuncts;

  if(!safety.is_true())
    conjuncts.push_back(G_exprt{safety});

  if(!liveness.is_true())
    conjuncts.push_back(G_exprt{F_exprt{liveness}});

  return conjunction(conjuncts);
}

/// Recursion for creating a safety automaton for a safety property.
/// * the property is converted into NNF on the fly.
/// * the monitor starts with the given "active" signal, which
///   is expected to stay on.
/// * the return value is the "safety" signal, or {} if not supported
std::optional<exprt> create_sva_monitor_rec(
  transition_systemt &transition_system,
  const exprt &active,
  const exprt &property_expr)
{
  if(!has_temporal_operator(property_expr))
  {
    // A state formula only. Needs to hold in "active" states only.
    return implies_exprt{active, property_expr};
  }
  else if(
    property_expr.id() == ID_not || property_expr.id() == ID_implies ||
    property_expr.id() == ID_nor || property_expr.id() == ID_nand ||
    property_expr.id() == ID_xor || property_expr.id() == ID_xnor)
  {
    // We rely on NNF.
    return {};
  }
  else if(property_expr.id() == ID_and)
  {
    // The conjunction of safety automata is built by conjoining the
    // safety signal.

    exprt::operandst conjuncts;

    for(auto &op : property_expr.operands())
    {
      auto rec = create_sva_monitor_rec(transition_system, active, op);
      if(!rec.has_value())
        return {};
      conjuncts.push_back(rec.value());
    }

    return conjunction(conjuncts);
  }
  else if(property_expr.id() == ID_or)
  {
    // Build automaton per disjunct.
    // Keep a state bit per automaton to record an unsafe state.
    // Signal an unsafe state when all subautomata signalled an unsafe state.
    return {};
  }
  else if(property_expr.id() == ID_sva_always)
  {
    // Nondeterministically guess when to start monitoring.
    auxiliary_symbolt always_activated_symbol{
      "sva-monitor::always_activated",
      bool_typet{},
      transition_system.main_symbol->mode};

    always_activated_symbol.is_state_var = true;
    always_activated_symbol.module = transition_system.main_symbol->module;
    always_activated_symbol.base_name = "always_activated";

    auto result1 =
      transition_system.symbol_table.insert(std::move(always_activated_symbol));
    CHECK_RETURN(result1.second);

    const auto always_activated_expr = result1.first.symbol_expr();

    // "always activated" is false in the initial state
    transition_system.trans_expr.init() = and_exprt{
      transition_system.trans_expr.init(), not_exprt{always_activated_expr}};

    auxiliary_symbolt always_active_symbol{
      "sva-monitor::always_active",
      bool_typet{},
      transition_system.main_symbol->mode};

    always_active_symbol.is_state_var = false;
    always_active_symbol.module = transition_system.main_symbol->module;
    always_active_symbol.base_name = "always_active";

    auto result2 =
      transition_system.symbol_table.insert(std::move(always_active_symbol));
    CHECK_RETURN(result2.second);

    const auto always_active_expr = result2.first.symbol_expr();

    auto always_activated_next_expr =
      exprt(ID_next_symbol, always_activated_expr.type());
    always_activated_next_expr.set(
      ID_identifier, always_activated_expr.get_identifier());
    transition_system.trans_expr.trans() = and_exprt{
      transition_system.trans_expr.trans(),
      equal_exprt{always_activated_next_expr, always_active_expr}};

    // recursion
    auto &op = to_sva_always_expr(property_expr).op();

    return create_sva_monitor_rec(transition_system, always_active_expr, op);
  }
  else if(property_expr.id() == ID_sva_s_nexttime)
  {
    // Simply wait one time frame.
    return {};
  }
  else
    return {}; // not supported
}

exprt sva_monitor_initial(transition_systemt &transition_system)
{
  auxiliary_symbolt initial_symbol{
    "sva-monitor::initial", bool_typet{}, transition_system.main_symbol->mode};

  initial_symbol.is_state_var = true;
  initial_symbol.module = transition_system.main_symbol->module;
  initial_symbol.base_name = "initial";

  auto result =
    transition_system.symbol_table.insert(std::move(initial_symbol));
  CHECK_RETURN(result.second);

  const auto symbol_expr = result.first.symbol_expr();

  // true in the initial state
  transition_system.trans_expr.init() =
    and_exprt{transition_system.trans_expr.init(), symbol_expr};

  // but false in subsequent states
  auto next_expr = exprt(ID_next_symbol, symbol_expr.type());
  next_expr.set(ID_identifier, symbol_expr.get_identifier());
  transition_system.trans_expr.trans() =
    and_exprt{transition_system.trans_expr.trans(), not_exprt{next_expr}};

  return symbol_expr;
}

void create_sva_monitor(
  transition_systemt &transition_system,
  ebmc_propertiest::propertyt &property)
{
  // Create the top-level "start" signal -- on in the initial states exactly.
  auto start = sva_monitor_initial(transition_system);

  // start recursion over property expression
  auto result =
    create_sva_monitor_rec(transition_system, start, property.normalized_expr);

  if(result.has_value())
    property.normalized_expr = G_exprt{result.value()};
}

void sva_monitor(
  transition_systemt &transition_system,
  ebmc_propertiest &properties)
{
  for(auto &property : properties.properties)
  {
    create_sva_monitor(transition_system, property);
  }
}
