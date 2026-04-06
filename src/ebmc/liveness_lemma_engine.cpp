/*******************************************************************\

Module: Liveness Lemma Engine

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Liveness Lemma Engine
///
/// Identifies safety properties that are ranking function lemmas
/// of the form
///
///   assert property (@(posedge clk) !live |=> rank < $past(rank));
///
/// and uses them to prove liveness properties of the form
///
///   assert property (@(posedge clk) s_eventually live);

#include "liveness_lemma_engine.h"

#include <util/arith_tools.h>
#include <util/simplify_expr.h>

#include <temporal-logic/ctl.h>
#include <temporal-logic/normalize_property.h>
#include <verilog/sva_expr.h>
#include <verilog/verilog_expr.h>

#include "ranking_function.h"

/// A liveness lemma
struct liveness_lemmat
{
  exprt live; // this condition is true infinitely often
};

/// Try to extract a ranking function-based liveness lemma from a normalized
/// (but not $past-instrumented) property expression.
/// Matches: always (live ∨ always[1:1](rank < $past(rank)))
/// which is the normalized form of: always (!live |=> rank < $past(rank))
static std::optional<liveness_lemmat>
extract_liveness_lemma(const exprt &normalized)
{
  // Must be sva_always p
  if(normalized.id() != ID_sva_always)
    return {};

  const auto &p = to_sva_always_expr(normalized).op();

  // p must be or(a, b) with exactly two operands
  if(p.id() != ID_or || p.operands().size() != 2)
    return {};

  // One operand is the "live" condition (possibly double-negated),
  // the other is sva_ranged_always[1:1](rank < $past(rank)).
  auto check = [](
                 const exprt &live,
                 const exprt &ranged_always) -> std::optional<liveness_lemmat>
  {
    const auto &ranged = to_sva_ranged_always_expr(ranged_always);

    // Check [1:1] range
    auto from_opt = numeric_cast<mp_integer>(ranged.from());
    if(!from_opt || *from_opt != 1)
      return {};

    auto to_opt = numeric_cast<mp_integer>(ranged.to());
    if(!to_opt || *to_opt != 1)
      return {};

    const auto &comparison = ranged.op();

    // Must be rank < $past(rank)
    if(comparison.id() != ID_lt)
      return {};

    const auto &lt = to_binary_relation_expr(comparison);

    if(lt.rhs().id() != ID_verilog_past)
      return {};

    const auto &past = to_verilog_past_expr(lt.rhs());

    // $past with 1 tick
    auto ticks_opt = numeric_cast<mp_integer>(past.ticks());
    if(!ticks_opt || *ticks_opt != 1)
      return {};

    // rank < $past(rank) — the two rank expressions must match
    if(lt.lhs() != past.what())
      return {};

    return liveness_lemmat{live};
  };

  auto &or_expr = to_or_expr(p);

  if(or_expr.op0().id() == ID_sva_ranged_always)
    return check(or_expr.op1(), or_expr.op0());
  else
    return check(or_expr.op0(), or_expr.op1());

  return {};
}

/// Returns the condition p from a liveness property
/// of the form always s_eventually p.
static std::optional<exprt> liveness_condition(const exprt &normalized)
{
  if(
    normalized.id() == ID_sva_always &&
    to_sva_always_expr(normalized).op().id() == ID_sva_s_eventually)
  {
    return to_sva_s_eventually_expr(to_sva_always_expr(normalized).op()).op();
  }

  return {};
}

property_checker_resultt liveness_lemma_engine(
  const cmdlinet &,
  const transition_systemt &transition_system,
  ebmc_propertiest &properties,
  const ebmc_solver_factoryt &, // unused
  message_handlert &)           // unused
{
  // Collect liveness lemmas from safety properties.
  std::vector<liveness_lemmat> lemmas;

  for(const auto &property : properties.properties)
  {
    if(property.is_proved() || property.is_assumption())
    {
      /// Try to extract a ranking function lemma from a normalized
      /// (but not $past-instrumented) property expression.
      auto normalized = normalize_property(property.original_expr);
      auto lemma = extract_liveness_lemma(normalized);
      if(lemma)
        lemmas.push_back(lemma.value());
    }
  }

  if(lemmas.empty())
    return property_checker_resultt{properties};

  const namespacet ns{transition_system.symbol_table};

  // Try to prove liveness properties using the collected safety lemmas.
  for(auto &property : properties.properties)
  {
    if(!property.is_unknown())
      continue;

    auto live_opt = liveness_condition(property.normalized_expr);

    if(!live_opt)
      continue;

    for(const auto &lemma : lemmas)
    {
      if(simplify_expr(equal_exprt{lemma.live, *live_opt}, ns).is_true())
      {
        property.proved("ranking function lemma");
        break;
      }
    }
  }

  return property_checker_resultt{properties};
}
