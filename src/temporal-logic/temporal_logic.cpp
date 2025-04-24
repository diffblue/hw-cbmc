/*******************************************************************\

Module: Temporal Logic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "temporal_logic.h"

#include <util/arith_tools.h>
#include <util/expr_util.h>

#include <verilog/sva_expr.h>

#include "ctl.h"
#include "ltl.h"

bool is_temporal_operator(const exprt &expr)
{
  return is_CTL_operator(expr) || is_LTL_operator(expr) ||
         is_LTL_past_operator(expr) || is_SVA_operator(expr) ||
         is_RTCTL_operator(expr) || expr.id() == ID_A || expr.id() == ID_E;
}

bool has_temporal_operator(const exprt &expr)
{
  return has_subexpr(expr, is_temporal_operator);
}

bool is_exists_path(const exprt &expr)
{
  return expr.id() == ID_sva_cover;
}

bool is_RTCTL_operator(const exprt &expr)
{
  auto id = expr.id();
  return id == ID_smv_EBF || id == ID_smv_ABF || id == ID_smv_EBG ||
         id == ID_smv_ABG || id == ID_smv_ABU || id == ID_smv_EBU;
}

bool has_RTCTL_operator(const exprt &expr)
{
  return has_subexpr(expr, is_RTCTL_operator);
}

bool is_CTL_operator(const exprt &expr)
{
  auto id = expr.id();
  return id == ID_AG || id == ID_EG || id == ID_AF || id == ID_EF ||
         id == ID_AX || id == ID_EX || id == ID_AU || id == ID_EU ||
         id == ID_AR || id == ID_ER;
}

bool has_CTL_operator(const exprt &expr)
{
  return has_subexpr(expr, is_CTL_operator);
}

bool is_CTL(const exprt &expr)
{
  auto non_CTL_operator = [](const exprt &expr) {
    return is_temporal_operator(expr) && !is_CTL_operator(expr);
  };

  return !has_subexpr(expr, non_CTL_operator);
}

bool is_LTL_operator(const exprt &expr)
{
  auto id = expr.id();
  return id == ID_G || id == ID_F || id == ID_X || id == ID_U || id == ID_R;
}

bool is_LTL_past_operator(const exprt &expr)
{
  auto id = expr.id();
  return id == ID_smv_H || id == ID_smv_bounded_H || id == ID_smv_O ||
         id == ID_smv_bounded_O || id == ID_smv_S || id == ID_smv_T ||
         id == ID_smv_Y || id == ID_smv_Z;
}

bool is_LTL(const exprt &expr)
{
  auto non_LTL_operator = [](const exprt &expr) {
    return is_temporal_operator(expr) && !is_LTL_operator(expr);
  };

  return !has_subexpr(expr, non_LTL_operator);
}

bool is_LTL_past(const exprt &expr)
{
  auto non_LTL_past_operator = [](const exprt &expr)
  { return is_temporal_operator(expr) && !is_LTL_past_operator(expr); };

  return !has_subexpr(expr, non_LTL_past_operator);
}

bool is_SVA_sequence_operator(const exprt &expr)
{
  auto id = expr.id();
  // Note that ID_sva_overlapped_followed_by, ID_sva_nonoverlapped_followed_by,
  // ID_sva_non_overlapped_implication and ID_sva_overlapped_implication
  // are property expressions, not sequence expressions.
  // Note that ID_sva_not does not yield a sequence expression.
  return id == ID_sva_and || id == ID_sva_or || id == ID_sva_cycle_delay ||
         id == ID_sva_cycle_delay_plus || id == ID_sva_cycle_delay_star ||
         id == ID_sva_sequence_concatenation ||
         id == ID_sva_sequence_intersect || id == ID_sva_sequence_first_match ||
         id == ID_sva_sequence_throughout || id == ID_sva_sequence_within ||
         id == ID_sva_sequence_goto_repetition ||
         id == ID_sva_sequence_consecutive_repetition ||
         id == ID_sva_sequence_non_consecutive_repetition ||
         id == ID_sva_sequence_repetition_star ||
         id == ID_sva_sequence_repetition_plus;
}

bool is_SVA_operator(const exprt &expr)
{
  auto id = expr.id();
  return is_SVA_sequence_operator(expr) || id == ID_sva_disable_iff ||
         id == ID_sva_accept_on || id == ID_sva_reject_on ||
         id == ID_sva_sync_accept_on || id == ID_sva_sync_reject_on ||
         id == ID_sva_always || id == ID_sva_s_always ||
         id == ID_sva_ranged_always || id == ID_sva_nexttime ||
         id == ID_sva_s_nexttime || id == ID_sva_indexed_nexttime ||
         id == ID_sva_until || id == ID_sva_s_until ||
         id == ID_sva_until_with || id == ID_sva_s_until_with ||
         id == ID_sva_eventually || id == ID_sva_s_eventually ||
         id == ID_sva_ranged_s_eventually || id == ID_sva_cycle_delay ||
         id == ID_sva_overlapped_implication ||
         id == ID_sva_non_overlapped_implication ||
         id == ID_sva_overlapped_followed_by ||
         id == ID_sva_nonoverlapped_followed_by ||
         id == ID_sva_sequence_property || id == ID_sva_weak ||
         id == ID_sva_strong || id == ID_sva_implicit_weak ||
         id == ID_sva_implicit_strong;
}

bool is_SVA(const exprt &expr)
{
  auto non_SVA_operator = [](const exprt &expr)
  { return is_temporal_operator(expr) && !is_SVA_operator(expr); };

  return !has_subexpr(expr, non_SVA_operator);
}

bool is_SVA_always_p(const exprt &expr)
{
  return expr.id() == ID_sva_always &&
         !has_temporal_operator(to_sva_always_expr(expr).op());
}

bool is_SVA_always_s_eventually_p(const exprt &expr)
{
  return expr.id() == ID_sva_always &&
         to_sva_always_expr(expr).op().id() == ID_sva_s_eventually &&
         !has_temporal_operator(
           to_sva_s_eventually_expr(to_sva_always_expr(expr).op()).op());
}

std::optional<exprt> LTL_to_CTL(exprt expr)
{
  // We map a subset of LTL to ACTL, following
  // Monika Maidl. "The common fragment of CTL and LTL"
  // http://dx.doi.org/10.1109/SFCS.2000.892332
  //
  // Specificially, we allow
  // * state predicates
  // * conjunctions of allowed formulas
  // * X φ, where φ is allowed
  // * F φ, where φ is allowed
  // * G φ, where φ is allowed
  if(!has_temporal_operator(expr))
  {
    return expr;
  }
  else if(expr.id() == ID_and)
  {
    for(auto &op : expr.operands())
    {
      auto rec = LTL_to_CTL(op);
      if(!rec.has_value())
        return {};
      op = *rec;
    }
    return expr;
  }
  else if(expr.id() == ID_X)
  {
    auto rec = LTL_to_CTL(to_X_expr(expr).op());
    if(rec.has_value())
      return AX_exprt{*rec};
    else
      return {};
  }
  else if(expr.id() == ID_F)
  {
    auto rec = LTL_to_CTL(to_F_expr(expr).op());
    if(rec.has_value())
      return AF_exprt{*rec};
    else
      return {};
  }
  else if(expr.id() == ID_G)
  {
    auto rec = LTL_to_CTL(to_G_expr(expr).op());
    if(rec.has_value())
      return AG_exprt{*rec};
    else
      return {};
  }
  else
    return {};
}

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
  ltl_sequence_matcht(exprt __cond, mp_integer __length)
    : cond(std::move(__cond)), length(std::move(__length))
  {
    PRECONDITION(length >= 0);
  }

  exprt cond;        // LTL
  mp_integer length; // match_end - match_start + 1

  bool empty() const
  {
    return length == 0;
  }
};

std::vector<ltl_sequence_matcht> LTL_sequence_matches(const exprt &sequence)
{
  if(!is_SVA_sequence_operator(sequence))
  {
    // atomic proposition
    return {{sequence, 1}};
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
        // Concatenation is overlapping, hence deduct one from
        // the length.
        auto delay = match_lhs.length - 1;
        auto rhs_delayed = n_Xes(delay, match_rhs.cond);
        result.emplace_back(
          and_exprt{match_lhs.cond, rhs_delayed},
          match_lhs.length + match_rhs.length - 1);
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
      for(auto &match : matches)
      {
        // delay as instructed
        match.length += from_int;
        match.cond = n_Xes(from_int, match.cond);
      }
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
        for(const auto &match : matches)
        {
          // delay as instructed
          auto new_match = match;
          new_match.length += from_int;
          new_match.cond = n_Xes(i, match.cond);
          new_matches.push_back(std::move(new_match));
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
      if(match.empty() && overlapped)
      {
        // ignore the empty match
      }
      else
      {
        auto delay = match.length + (overlapped ? 0 : 1) - 1;
        auto delayed_property = n_Xes(delay, property_rec.value());
        conjuncts.push_back(implies_exprt{match.cond, delayed_property});
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
      if(match.empty() && overlapped)
      {
        // ignore the empty match
      }
      else
      {
        auto delay = match.length + (overlapped ? 0 : 1) - 1;
        auto delayed_property = n_Xes(delay, property_rec.value());
        disjuncts.push_back(and_exprt{match.cond, delayed_property});
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
      if(!match.empty())
        disjuncts.push_back(match.cond);
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
