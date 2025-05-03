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
