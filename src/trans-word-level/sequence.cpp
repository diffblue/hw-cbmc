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
    // For the intersection of the two operand sequences to match, the following
    // must hold:
    // — Both the operands shall match.
    // — The lengths of the two matches of the operand sequences shall be the same.
    auto &intersect = to_sva_sequence_intersect_expr(expr);

    const auto lhs_match_points =
      instantiate_sequence(intersect.lhs(), t, no_timeframes);
    const auto rhs_match_points =
      instantiate_sequence(intersect.rhs(), t, no_timeframes);

    std::vector<std::pair<mp_integer, exprt>> result;

    for(auto &lhs_match : lhs_match_points)
    {
      for(auto &rhs_match : rhs_match_points)
      {
        // Same length?
        if(lhs_match.first == rhs_match.first)
        {
          result.emplace_back(
            lhs_match.first, and_exprt{lhs_match.second, rhs_match.second});
        }
      }
    }

    return result;
  }
  else if(expr.id() == ID_sva_sequence_first_match)
  {
    PRECONDITION(false);
  }
  else if(expr.id() == ID_sva_sequence_throughout)
  {
    // IEEE 1800-2017 16.9.9
    // exp throughout seq matches along an interval provided
    // - seq matches along the interval and
    // - exp evaluates to true at each clock tick of the interval.
    auto &throughout = to_sva_sequence_throughout_expr(expr);

    const auto rhs_match_points =
      instantiate_sequence(throughout.rhs(), t, no_timeframes);

    std::vector<std::pair<mp_integer, exprt>> result;

    for(auto &rhs_match : rhs_match_points)
    {
      exprt::operandst conjuncts = {rhs_match.second};

      for(mp_integer new_t = t; new_t <= rhs_match.first; ++new_t)
      {
        auto obligations =
          property_obligations(throughout.lhs(), new_t, no_timeframes);
        conjuncts.push_back(obligations.conjunction().second);
      }

      result.emplace_back(rhs_match.first, conjunction(conjuncts));
    }

    return result;
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
  else if(expr.id() == ID_sva_sequence_consecutive_repetition)
  {
    // x[*n] is syntactic sugar for x ##1 ... ##1 x, with n repetitions
    auto &repetition = to_sva_sequence_consecutive_repetition_expr(expr);
    return instantiate_sequence(repetition.lower(), t, no_timeframes);
  }
  else
  {
    // not a sequence, evaluate as state predicate
    auto obligations = property_obligations(expr, t, no_timeframes);
    return {obligations.conjunction()};
  }
}
