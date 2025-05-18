/*******************************************************************\

Module: SVA to LTL

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>

#include <verilog/sva_expr.h>

#include "ltl.h"
#include "temporal_logic.h"

static exprt n_Xes(mp_integer n, exprt op)
{
  PRECONDITION(n >= 0);
  if(n == 0)
    return op;
  else
    return n_Xes(n - 1, X_exprt{std::move(op)});
}

// Returns a set of match conditions (given as LTL formula)
struct ltl_sequence_matcht
{
  // the empty match
  ltl_sequence_matcht()
  {
  }

  // a match of length 1
  explicit ltl_sequence_matcht(exprt __cond) : cond_vector{1, std::move(__cond)}
  {
  }

  std::vector<exprt> cond_vector;

  std::size_t length()
  {
    return cond_vector.size();
  }

  bool empty_match() const
  {
    return cond_vector.empty();
  }

  // c0 ∧ X c1 ∧ XX c2 ....
  exprt cond_expr() const
  {
    exprt::operandst conjuncts;
    conjuncts.reserve(cond_vector.size());
    for(std::size_t i = 0; i < cond_vector.size(); i++)
    {
      auto &c = cond_vector[i];
      if(!c.is_true())
        conjuncts.push_back(n_Xes(i, c));
    }
    return conjunction(conjuncts);
  }

  // generate true ##1 ... ##1 true with length n
  static ltl_sequence_matcht true_match(const mp_integer &n)
  {
    ltl_sequence_matcht result;
    for(mp_integer i; i < n; ++i)
      result.cond_vector.push_back(true_exprt{});
    return result;
  }
};

// nonoverlapping concatenation
ltl_sequence_matcht concat(ltl_sequence_matcht a, const ltl_sequence_matcht &b)
{
  a.cond_vector.insert(
    a.cond_vector.end(), b.cond_vector.begin(), b.cond_vector.end());
  return a;
}

// overlapping concatenation
ltl_sequence_matcht
overlapping_concat(ltl_sequence_matcht a, ltl_sequence_matcht b)
{
  PRECONDITION(!a.empty_match());
  PRECONDITION(!b.empty_match());
  auto a_last = a.cond_vector.back();
  a.cond_vector.pop_back();
  b.cond_vector.front() = conjunction({a_last, b.cond_vector.front()});
  return concat(std::move(a), b);
}

std::vector<ltl_sequence_matcht> LTL_sequence_matches(const exprt &sequence)
{
  if(sequence.id() == ID_sva_boolean)
  {
    // atomic proposition
    return {ltl_sequence_matcht{to_sva_boolean_expr(sequence).op()}};
  }
  else if(sequence.id() == ID_sva_sequence_concatenation)
  {
    auto &concatenation = to_sva_sequence_concatenation_expr(sequence);
    auto matches_lhs = LTL_sequence_matches(concatenation.lhs());
    auto matches_rhs = LTL_sequence_matches(concatenation.rhs());

    if(matches_lhs.empty() || matches_rhs.empty())
      return {};

    std::vector<ltl_sequence_matcht> result;

    // cross product
    for(auto &match_lhs : matches_lhs)
      for(auto &match_rhs : matches_rhs)
      {
        // Sequence concatenation is overlapping
        auto new_match = overlapping_concat(match_lhs, match_rhs);
        CHECK_RETURN(
          new_match.length() == match_lhs.length() + match_rhs.length() - 1);
        result.push_back(std::move(new_match));
      }
    return result;
  }
  else if(sequence.id() == ID_sva_cycle_delay)
  {
    auto &delay = to_sva_cycle_delay_expr(sequence);
    auto matches = LTL_sequence_matches(delay.op());
    auto from_int = numeric_cast_v<mp_integer>(delay.from());

    if(matches.empty())
      return {};

    if(delay.to().is_nil())
    {
      // delay as instructed
      auto delay_sequence = ltl_sequence_matcht::true_match(from_int);

      for(auto &match : matches)
        match = concat(delay_sequence, match);

      return matches;
    }
    else if(delay.to().id() == ID_infinity)
    {
      return {}; // can't encode
    }
    else if(delay.to().is_constant())
    {
      auto to_int = numeric_cast_v<mp_integer>(to_constant_expr(delay.to()));
      std::vector<ltl_sequence_matcht> new_matches;

      for(mp_integer i = from_int; i <= to_int; ++i)
      {
        // delay as instructed
        auto delay_sequence = ltl_sequence_matcht::true_match(i);

        for(const auto &match : matches)
        {
          new_matches.push_back(concat(delay_sequence, match));
        }
      }

      return new_matches;
    }
    else
      return {};
  }
  else
  {
    return {}; // unsupported
  }
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
      auto lower_int = numeric_cast_v<mp_integer>(ranged_always.lower());

      // Is there an upper end of the range?
      if(ranged_always.upper().is_constant())
      {
        // upper end set
        auto upper_int =
          numeric_cast_v<mp_integer>(to_constant_expr(ranged_always.upper()));
        PRECONDITION(upper_int >= lower_int);
        auto diff = upper_int - lower_int;

        exprt::operandst conjuncts;

        for(auto i = 0; i <= diff; i++)
          conjuncts.push_back(n_Xes(i, rec.value()));

        return n_Xes(lower_int, conjunction(conjuncts));
      }
      else if(ranged_always.upper().id() == ID_infinity)
      {
        // always [l:$] op ---> X ... X G op
        return n_Xes(lower_int, G_exprt{rec.value()});
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
      auto lower_int = numeric_cast_v<mp_integer>(ranged_always.lower());
      auto upper_int = numeric_cast_v<mp_integer>(ranged_always.upper());
      PRECONDITION(upper_int >= lower_int);
      auto diff = upper_int - lower_int;

      exprt::operandst conjuncts;

      for(auto i = 0; i <= diff; i++)
        conjuncts.push_back(n_Xes(i, rec.value()));

      return n_Xes(lower_int, conjunction(conjuncts));
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
        conjuncts.push_back(implies_exprt{match.cond_expr(), delayed_property});
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
        disjuncts.push_back(and_exprt{match.cond_expr(), delayed_property});
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
        disjuncts.push_back(match.cond_expr());
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
