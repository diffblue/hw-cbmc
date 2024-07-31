/*******************************************************************\

Module: Temporal Logic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "temporal_logic.h"

#include <util/expr_util.h>

bool is_temporal_operator(const exprt &expr)
{
  return is_CTL_operator(expr) || is_LTL_operator(expr) ||
         is_SVA_sequence(expr) || expr.id() == ID_A || expr.id() == ID_E ||
         expr.id() == ID_sva_always || expr.id() == ID_sva_always ||
         expr.id() == ID_sva_ranged_always || expr.id() == ID_sva_nexttime ||
         expr.id() == ID_sva_s_nexttime || expr.id() == ID_sva_until ||
         expr.id() == ID_sva_s_until || expr.id() == ID_sva_until_with ||
         expr.id() == ID_sva_s_until_with || expr.id() == ID_sva_eventually ||
         expr.id() == ID_sva_s_eventually || expr.id() == ID_sva_cycle_delay ||
         expr.id() == ID_sva_overlapped_followed_by ||
         expr.id() == ID_sva_nonoverlapped_followed_by;
}

bool has_temporal_operator(const exprt &expr)
{
  return has_subexpr(expr, is_temporal_operator);
}

bool is_exists_path(const exprt &expr)
{
  return expr.id() == ID_sva_cover;
}

bool is_CTL_operator(const exprt &expr)
{
  auto id = expr.id();
  return id == ID_AG || id == ID_EG || id == ID_AF || id == ID_EF ||
         id == ID_AX || id == ID_EX || id == ID_AU || id == ID_EU ||
         id == ID_AR || id == ID_ER;
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

bool is_LTL(const exprt &expr)
{
  auto non_LTL_operator = [](const exprt &expr) {
    return is_temporal_operator(expr) && !is_LTL_operator(expr);
  };

  return !has_subexpr(expr, non_LTL_operator);
}

bool is_SVA_sequence(const exprt &expr)
{
  auto id = expr.id();
  // Note that ID_sva_overlapped_followed_by and ID_sva_nonoverlapped_followed_by
  // are property expressions, not sequence expressions.
  // Note that ID_sva_not does not yield a sequence expression.
  return id == ID_sva_and || id == ID_sva_or ||
         id == ID_sva_overlapped_implication ||
         id == ID_sva_non_overlapped_implication || id == ID_sva_cycle_delay ||
         id == ID_sva_sequence_concatenation ||
         id == ID_sva_sequence_intersect || id == ID_sva_sequence_first_match ||
         id == ID_sva_sequence_throughout || id == ID_sva_sequence_within;
}
