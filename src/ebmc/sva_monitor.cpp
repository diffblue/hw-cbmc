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
/// * the property is assumed to be in NNF.
/// * the monitor starts with the given "start" signal
/// * the return value is the "safety" signal, or {} if not supported
std::optional<exprt> create_sva_safety_monitor_rec(
  transition_systemt &transition_system,
  const exprt &start,
  const exprt &property_expr)
{
  if(!has_temporal_operator(property_expr))
  {
    // A state formula only. Needs to hold in "start" states only.
    return and_exprt{start, property_expr};
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
      auto rec = create_sva_safety_monitor_rec(transition_system, start, op);
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
    //auto &op = to_sva_always_expr(expr).op();
    //return create_sva_safety_monitor_rec(transition_system, op);
    return {};
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
  return nil_exprt{};
}

/// top-level formula
std::optional<monitor_resultt>
create_sva_monitor(transition_systemt &transition_system, exprt property_expr)
{
  if(property_expr.id() == ID_sva_always)
  {
    auto &op = to_sva_always_expr(property_expr);

    // Special-case "always p".
    if(!has_temporal_operator(op))
      return monitor_resultt{.safety = op};

    // Create the top-level "start" signal -- on in the initial states exactly.
    auto start = sva_monitor_initial(transition_system);

    // always X
    auto result_rec =
      create_sva_safety_monitor_rec(transition_system, start, op);
    if(result_rec.has_value())
      return monitor_resultt{.safety = result_rec.value()};
  }

  return {}; // not supported
}

void create_sva_monitor(
  transition_systemt &transition_system,
  ebmc_propertiest::propertyt &property)
{
  auto result = create_sva_monitor(transition_system, property.normalized_expr);

  if(result.has_value())
    property.normalized_expr = result.value().as_LTL();
}

void sva_monitor(
  transition_systemt &transition_system,
  ebmc_propertiest &properties)
{
  for(auto &property : properties.properties)
  {
    if(has_SVA_operator(property.normalized_expr))
      create_sva_monitor(transition_system, property);
  }
}
