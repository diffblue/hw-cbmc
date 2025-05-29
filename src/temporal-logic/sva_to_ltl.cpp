/*******************************************************************\

Module: SVA to LTL

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>

#include <verilog/sva_expr.h>

#include "ltl.h"
#include "sva_sequence_match.h"
#include "temporal_logic.h"

static exprt n_Xes(mp_integer n, exprt op)
{
  PRECONDITION(n >= 0);
  if(n == 0)
    return op;
  else
    return n_Xes(n - 1, X_exprt{std::move(op)});
}

// c0 ∧ X c1 ∧ XX c2 ....
static exprt ltl(const sva_sequence_matcht &match)
{
  exprt::operandst conjuncts;
  conjuncts.reserve(match.cond_vector.size());
  for(std::size_t i = 0; i < match.cond_vector.size(); i++)
  {
    auto &c = match.cond_vector[i];
    if(!c.is_true())
      conjuncts.push_back(n_Xes(i, c));
  }
  return conjunction(conjuncts);
}

/// takes an SVA property as input, and returns an equivalent LTL property,
/// or otherwise {}.
std::optional<exprt> SVA_to_LTL(exprt expr)
{
  // Some SVA is directly mappable to LTL
  if(expr.id() == ID_sva_always)
  {
    auto rec = SVA_to_LTL(to_sva_always_expr(expr).op());
    if(rec.has_value())
      return G_exprt{rec.value()};
    else
      return {};
  }
  else if(expr.id() == ID_sva_ranged_always)
  {
    auto &ranged_always = to_sva_ranged_always_expr(expr);
    auto rec = SVA_to_LTL(ranged_always.op());
    if(rec.has_value())
    {
      // always [l:u] op ---> X ... X (op ∧ X op ∧ ... ∧ X ... X op)
      auto from_int = numeric_cast_v<mp_integer>(ranged_always.from());

      // Is there an upper end of the range?
      if(ranged_always.to().is_constant())
      {
        // upper end set
        auto to_int =
          numeric_cast_v<mp_integer>(to_constant_expr(ranged_always.to()));
        PRECONDITION(to_int >= from_int);
        auto diff = to_int - from_int;

        exprt::operandst conjuncts;

        for(auto i = 0; i <= diff; i++)
          conjuncts.push_back(n_Xes(i, rec.value()));

        return n_Xes(from_int, conjunction(conjuncts));
      }
      else if(ranged_always.to().id() == ID_infinity)
      {
        // always [l:$] op ---> X ... X G op
        return n_Xes(from_int, G_exprt{rec.value()});
      }
      else
        PRECONDITION(false);
    }
    else
      return {};
  }
  else if(expr.id() == ID_sva_s_always)
  {
    auto &ranged_always = to_sva_s_always_expr(expr);
    auto rec = SVA_to_LTL(ranged_always.op());
    if(rec.has_value())
    {
      // s_always [l:u] op ---> X ... X (op ∧ X op ∧ ... ∧ X ... X op)
      auto from_int = numeric_cast_v<mp_integer>(ranged_always.from());
      auto to_int = numeric_cast_v<mp_integer>(ranged_always.to());
      PRECONDITION(to_int >= from_int);
      auto diff = to_int - from_int;

      exprt::operandst conjuncts;

      for(auto i = 0; i <= diff; i++)
        conjuncts.push_back(n_Xes(i, rec.value()));

      return n_Xes(from_int, conjunction(conjuncts));
    }
    else
      return {};
  }
  else if(expr.id() == ID_sva_s_eventually)
  {
    auto rec = SVA_to_LTL(to_sva_s_eventually_expr(expr).op());
    if(rec.has_value())
      return F_exprt{rec.value()};
    else
      return {};
  }
  else if(expr.id() == ID_sva_s_nexttime)
  {
    auto rec = SVA_to_LTL(to_sva_s_nexttime_expr(expr).op());
    if(rec.has_value())
      return X_exprt{rec.value()};
    else
      return {};
  }
  else if(expr.id() == ID_sva_nexttime)
  {
    auto rec = SVA_to_LTL(to_sva_nexttime_expr(expr).op());
    if(rec.has_value())
      return X_exprt{rec.value()};
    else
      return {};
  }
  else if(
    expr.id() == ID_sva_overlapped_implication ||
    expr.id() == ID_sva_non_overlapped_implication)
  {
    auto &implication = to_sva_implication_base_expr(expr);
    auto matches = LTL_sequence_matches(implication.sequence());

    if(matches.empty())
      return {};

    // All matches must be followed
    // by the property being true
    exprt::operandst conjuncts;

    auto property_rec = SVA_to_LTL(implication.property());

    if(!property_rec.has_value())
      return {};

    for(auto &match : matches)
    {
      const auto overlapped = expr.id() == ID_sva_overlapped_implication;
      if(match.empty_match() && overlapped)
      {
        // ignore the empty match
      }
      else
      {
        auto delay = match.length() + (overlapped ? 0 : 1) - 1;
        auto delayed_property = n_Xes(delay, property_rec.value());
        conjuncts.push_back(implies_exprt{ltl(match), delayed_property});
      }
    }

    return conjunction(conjuncts);
  }
  else if(
    expr.id() == ID_sva_nonoverlapped_followed_by ||
    expr.id() == ID_sva_overlapped_followed_by)
  {
    auto &followed_by = to_sva_followed_by_expr(expr);
    auto matches = LTL_sequence_matches(followed_by.sequence());

    if(matches.empty())
      return {};

    // There must be at least one match that is followed
    // by the property being true
    exprt::operandst disjuncts;

    auto property_rec = SVA_to_LTL(followed_by.property());

    if(!property_rec.has_value())
      return {};

    for(auto &match : matches)
    {
      const auto overlapped = expr.id() == ID_sva_overlapped_followed_by;
      if(match.empty_match() && overlapped)
      {
        // ignore the empty match
      }
      else
      {
        auto delay = match.length() + (overlapped ? 0 : 1) - 1;
        auto delayed_property = n_Xes(delay, property_rec.value());
        disjuncts.push_back(and_exprt{ltl(match), delayed_property});
      }
    }

    return disjunction(disjuncts);
  }
  else if(expr.id() == ID_sva_sequence_property)
  {
    // should have been turned into sva_implicit_weak or sva_implicit_strong
    PRECONDITION(false);
  }
  else if(
    expr.id() == ID_sva_weak || expr.id() == ID_sva_strong ||
    expr.id() == ID_sva_implicit_weak || expr.id() == ID_sva_implicit_strong)
  {
    auto &sequence = to_sva_sequence_property_expr_base(expr).sequence();

    // evaluates to true if there's at least one non-empty match of the sequence
    auto matches = LTL_sequence_matches(sequence);

    if(matches.empty())
      return {};

    exprt::operandst disjuncts;

    for(auto &match : matches)
    {
      if(!match.empty_match())
        disjuncts.push_back(ltl(match));
    }

    return disjunction(disjuncts);
  }
  else if(expr.id() == ID_sva_s_until)
  {
    auto &until = to_sva_s_until_expr(expr);
    auto rec_lhs = SVA_to_LTL(until.lhs());
    auto rec_rhs = SVA_to_LTL(until.rhs());
    if(rec_lhs.has_value() && rec_rhs.has_value())
      return U_exprt{rec_lhs.value(), rec_rhs.value()};
    else
      return {};
  }
  else if(expr.id() == ID_sva_s_until_with)
  {
    // This is release with swapped operands
    auto &until_with = to_sva_s_until_with_expr(expr);
    auto rec_lhs = SVA_to_LTL(until_with.lhs());
    auto rec_rhs = SVA_to_LTL(until_with.rhs());
    if(rec_lhs.has_value() && rec_rhs.has_value())
      return R_exprt{rec_rhs.value(), rec_lhs.value()}; // swapped
    else
      return {};
  }
  else if(!has_temporal_operator(expr))
  {
    return expr;
  }
  else if(
    expr.id() == ID_and || expr.id() == ID_implies || expr.id() == ID_or ||
    expr.id() == ID_not)
  {
    for(auto &op : expr.operands())
    {
      auto rec = SVA_to_LTL(op);
      if(!rec.has_value())
        return {};
      op = rec.value();
    }
    return expr;
  }
  else
    return {};
}
