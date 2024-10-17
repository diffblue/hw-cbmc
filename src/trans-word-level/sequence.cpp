/*******************************************************************\

Module: Encoding SVA sequences

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "sequence.h"

#include <util/ebmc_util.h>

#include <verilog/sva_expr.h>

#include "obligations.h"
#include "property.h"

std::vector<std::pair<mp_integer, exprt>> instantiate_sequence(
  exprt expr,
  const mp_integer &t,
  const mp_integer &no_timeframes)
{
  if(expr.id() == ID_sva_cycle_delay) // ##[1:2] something
  {
    auto &sva_cycle_delay_expr = to_sva_cycle_delay_expr(expr);

    if(sva_cycle_delay_expr.to().is_nil()) // ##1 something
    {
      mp_integer offset;
      if(to_integer_non_constant(sva_cycle_delay_expr.from(), offset))
        throw "failed to convert sva_cycle_delay offset";

      const auto u = t + offset;

      // Do we exceed the bound? Make it 'true'
      if(u >= no_timeframes)
      {
        DATA_INVARIANT(no_timeframes != 0, "must have timeframe");
        return {{no_timeframes - 1, true_exprt()}};
      }
      else
        return instantiate_sequence(
          sva_cycle_delay_expr.op(), u, no_timeframes);
    }
    else
    {
      mp_integer from, to;
      if(to_integer_non_constant(sva_cycle_delay_expr.from(), from))
        throw "failed to convert sva_cycle_delay offsets";

      if(sva_cycle_delay_expr.to().id() == ID_infinity)
      {
        DATA_INVARIANT(no_timeframes != 0, "must have timeframe");
        to = no_timeframes - 1;
      }
      else if(to_integer_non_constant(sva_cycle_delay_expr.to(), to))
        throw "failed to convert sva_cycle_delay offsets";

      auto lower = t + from;
      auto upper = t + to;

      // Do we exceed the bound? Make it 'true'
      if(upper >= no_timeframes)
      {
        DATA_INVARIANT(no_timeframes != 0, "must have timeframe");
        return {{no_timeframes - 1, true_exprt()}};
      }

      std::vector<std::pair<mp_integer, exprt>> match_points;

      for(mp_integer u = lower; u <= upper; ++u)
      {
        auto sub_result =
          instantiate_sequence(sva_cycle_delay_expr.op(), u, no_timeframes);
        for(auto &match_point : sub_result)
          match_points.push_back(match_point);
      }

      return match_points;
    }
  }
  else if(
    expr.id() == ID_sva_sequence_concatenation ||
    expr.id() == ID_sva_overlapped_implication ||
    expr.id() == ID_sva_non_overlapped_implication)
  {
    auto &implication = to_binary_expr(expr);
    std::vector<std::pair<mp_integer, exprt>> result;

    // This is the product of the match points on the LHS and RHS
    const auto lhs_match_points =
      instantiate_sequence(implication.lhs(), t, no_timeframes);
    for(auto &lhs_match_point : lhs_match_points)
    {
      // The RHS of the non-overlapped implication starts one timeframe later
      auto t_rhs = expr.id() == ID_sva_non_overlapped_implication
                     ? lhs_match_point.first + 1
                     : lhs_match_point.first;

      // Do we exceed the bound? Make it 'true'
      if(t_rhs >= no_timeframes)
      {
        DATA_INVARIANT(no_timeframes != 0, "must have timeframe");
        return {{no_timeframes - 1, true_exprt()}};
      }

      const auto rhs_match_points =
        instantiate_sequence(implication.rhs(), t_rhs, no_timeframes);

      for(auto &rhs_match_point : rhs_match_points)
      {
        exprt cond;
        if(expr.id() == ID_sva_sequence_concatenation)
        {
          cond = and_exprt{lhs_match_point.second, rhs_match_point.second};
        }
        else if(
          expr.id() == ID_sva_overlapped_implication ||
          expr.id() == ID_sva_non_overlapped_implication)
        {
          cond = implies_exprt{lhs_match_point.second, rhs_match_point.second};
        }
        else
          PRECONDITION(false);

        result.push_back({rhs_match_point.first, cond});
      }
    }

    return result;
  }
  else if(expr.id() == ID_sva_sequence_intersect)
  {
    // IEEE 1800-2017 16.9.6
    PRECONDITION(false);
  }
  else if(expr.id() == ID_sva_sequence_first_match)
  {
    PRECONDITION(false);
  }
  else if(expr.id() == ID_sva_sequence_throughout)
  {
    PRECONDITION(false);
  }
  else if(expr.id() == ID_sva_sequence_within)
  {
    PRECONDITION(false);
  }
  else if(expr.id() == ID_sva_and)
  {
    // IEEE 1800-2017 16.9.5
    // 1. Both operands must match.
    // 2. Both sequences start at the same time.
    // 3. The end time of the composite sequence is
    //    the end time of the operand sequence that completes last.
    // Condition (3) is TBD.
    obligationst obligations;

    for(auto &op : expr.operands())
    {
      obligations.add(property_obligations(op, t, no_timeframes));
    }

    return {obligations.conjunction()};
  }
  else if(expr.id() == ID_sva_or)
  {
    // IEEE 1800-2017 16.9.7
    // The set of matches of a or b is the set union of the matches of a
    // and the matches of b.
    std::vector<std::pair<mp_integer, exprt>> result;

    for(auto &op : expr.operands())
      for(auto &match_point : instantiate_sequence(op, t, no_timeframes))
        result.push_back(match_point);

    return result;
  }
  else if(expr.id() == ID_sva_strong || expr.id() == ID_sva_weak)
  {
    // not distinguished
    auto &op = to_unary_expr(expr).op();
    return instantiate_sequence(op, t, no_timeframes);
  }
  else if(expr.id() == ID_sva_cycle_delay_plus)
  {
    auto new_expr = sva_s_eventually_exprt{
      sva_s_nexttime_exprt{to_sva_cycle_delay_plus_expr(expr).op()}};
    auto obligations = property_obligations(new_expr, t, no_timeframes);
    return {obligations.conjunction()};
  }
  else if(expr.id() == ID_sva_cycle_delay_star)
  {
    auto new_expr =
      sva_s_eventually_exprt{to_sva_cycle_delay_star_expr(expr).op()};
    auto obligations = property_obligations(new_expr, t, no_timeframes);
    return {obligations.conjunction()};
  }
  else
  {
    // not a sequence, evaluate as state predicate
    auto obligations = property_obligations(expr, t, no_timeframes);
    return {obligations.conjunction()};
  }
}
