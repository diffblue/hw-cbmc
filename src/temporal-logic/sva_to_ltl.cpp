/*******************************************************************\

Module: SVA to LTL

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "sva_to_ltl.h"

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

/// takes an SVA property as input, and returns an equivalent LTL property
exprt SVA_to_LTL(exprt expr)
{
  // Some SVA is directly mappable to LTL
  if(expr.id() == ID_sva_always)
  {
    auto rec = SVA_to_LTL(to_sva_always_expr(expr).op());
    return G_exprt{rec};
  }
  else if(expr.id() == ID_sva_ranged_always)
  {
    auto &ranged_always = to_sva_ranged_always_expr(expr);
    auto rec = SVA_to_LTL(ranged_always.op());
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
        conjuncts.push_back(n_Xes(i, rec));

      return n_Xes(from_int, conjunction(conjuncts));
    }
    else if(ranged_always.to().id() == ID_infinity)
    {
      // always [l:$] op ---> X ... X G op
      return n_Xes(from_int, G_exprt{rec});
    }
    else
      PRECONDITION(false);
  }
  else if(expr.id() == ID_sva_s_always)
  {
    auto &ranged_always = to_sva_s_always_expr(expr);
    auto rec = SVA_to_LTL(ranged_always.op());

    // s_always [l:u] op ---> X ... X (op ∧ X op ∧ ... ∧ X ... X op)
    auto from_int = numeric_cast_v<mp_integer>(ranged_always.from());
    auto to_int = numeric_cast_v<mp_integer>(ranged_always.to());
    PRECONDITION(to_int >= from_int);
    auto diff = to_int - from_int;

    exprt::operandst conjuncts;

    for(auto i = 0; i <= diff; i++)
      conjuncts.push_back(n_Xes(i, rec));

    return n_Xes(from_int, conjunction(conjuncts));
  }
  else if(expr.id() == ID_sva_s_eventually)
  {
    auto rec = SVA_to_LTL(to_sva_s_eventually_expr(expr).op());
    return F_exprt{std::move(rec)};
  }
  else if(expr.id() == ID_sva_s_nexttime)
  {
    auto rec = SVA_to_LTL(to_sva_s_nexttime_expr(expr).op());
    return X_exprt{std::move(rec)};
  }
  else if(expr.id() == ID_sva_nexttime)
  {
    auto rec = SVA_to_LTL(to_sva_nexttime_expr(expr).op());
    return X_exprt{std::move(rec)};
  }
  else if(
    expr.id() == ID_sva_overlapped_implication ||
    expr.id() == ID_sva_non_overlapped_implication)
  {
    auto &implication = to_sva_implication_base_expr(expr);

    try
    {
      auto matches = LTL_sequence_matches(implication.sequence());

      // All matches must be followed
      // by the property being true
      exprt::operandst conjuncts;

      auto property_rec = SVA_to_LTL(implication.property());

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
          auto delayed_property = n_Xes(delay, property_rec);
          conjuncts.push_back(implies_exprt{ltl(match), delayed_property});
        }
      }

      return conjunction(conjuncts);
    }
    catch(sva_sequence_match_unsupportedt error)
    {
      throw sva_to_ltl_unsupportedt{std::move(error.expr)};
    }
  }
  else if(
    expr.id() == ID_sva_nonoverlapped_followed_by ||
    expr.id() == ID_sva_overlapped_followed_by)
  {
    auto &followed_by = to_sva_followed_by_expr(expr);

    try
    {
      auto matches = LTL_sequence_matches(followed_by.sequence());

      // There must be at least one match that is followed
      // by the property being true
      exprt::operandst disjuncts;

      auto property_rec = SVA_to_LTL(followed_by.property());

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
          auto delayed_property = n_Xes(delay, property_rec);
          disjuncts.push_back(and_exprt{ltl(match), delayed_property});
        }
      }

      return disjunction(disjuncts);
    }
    catch(sva_sequence_match_unsupportedt error)
    {
      throw sva_to_ltl_unsupportedt{std::move(error.expr)};
    }
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

    try
    {
      // evaluates to true if there's at least one non-empty match of the sequence
      auto matches = LTL_sequence_matches(sequence);

      exprt::operandst disjuncts;

      for(auto &match : matches)
      {
        if(!match.empty_match())
          disjuncts.push_back(ltl(match));
      }

      return disjunction(disjuncts);
    }
    catch(sva_sequence_match_unsupportedt error)
    {
      throw sva_to_ltl_unsupportedt{std::move(error.expr)};
    }
  }
  else if(expr.id() == ID_sva_s_until)
  {
    auto &until = to_sva_s_until_expr(expr);
    auto rec_lhs = SVA_to_LTL(until.lhs());
    auto rec_rhs = SVA_to_LTL(until.rhs());
    return U_exprt{rec_lhs, rec_rhs};
  }
  else if(expr.id() == ID_sva_s_until_with)
  {
    // This is release with swapped operands
    auto &until_with = to_sva_s_until_with_expr(expr);
    auto rec_lhs = SVA_to_LTL(until_with.lhs());
    auto rec_rhs = SVA_to_LTL(until_with.rhs());
    return R_exprt{rec_rhs, rec_lhs}; // swapped
  }
  else if(!has_temporal_operator(expr))
  {
    return expr;
  }
  else if(expr.id() == ID_sva_implies)
  {
    // maps cleanly to 'implies'
    auto &sva_implies = to_sva_implies_expr(expr);
    auto rec_lhs = SVA_to_LTL(sva_implies.lhs());
    auto rec_rhs = SVA_to_LTL(sva_implies.rhs());
    return implies_exprt{rec_rhs, rec_lhs};
  }
  else if(expr.id() == ID_sva_iff)
  {
    // maps cleanly to =
    auto &sva_iff = to_sva_iff_expr(expr);
    auto rec_lhs = SVA_to_LTL(sva_iff.lhs());
    auto rec_rhs = SVA_to_LTL(sva_iff.rhs());
    return equal_exprt{rec_rhs, rec_lhs};
  }
  else if(expr.id() == ID_sva_and)
  {
    // maps cleanly to Boolean and
    auto &sva_iff = to_sva_iff_expr(expr);
    auto rec_lhs = SVA_to_LTL(sva_iff.lhs());
    auto rec_rhs = SVA_to_LTL(sva_iff.rhs());
    return and_exprt{rec_rhs, rec_lhs};
  }
  else if(expr.id() == ID_sva_or)
  {
    // maps cleanly to Boolean or
    auto &sva_iff = to_sva_iff_expr(expr);
    auto rec_lhs = SVA_to_LTL(sva_iff.lhs());
    auto rec_rhs = SVA_to_LTL(sva_iff.rhs());
    return or_exprt{rec_rhs, rec_lhs};
  }
  else if(
    expr.id() == ID_and || expr.id() == ID_implies || expr.id() == ID_or ||
    expr.id() == ID_not)
  {
    for(auto &op : expr.operands())
    {
      auto rec = SVA_to_LTL(op);
      op = rec;
    }
    return expr;
  }
  else
  {
    throw sva_to_ltl_unsupportedt{std::move(expr)};
  }
}
