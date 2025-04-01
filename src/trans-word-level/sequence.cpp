/*******************************************************************\

Module: Encoding SVA sequences

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "sequence.h"

#include <util/arith_tools.h>
#include <util/ebmc_util.h>

#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

#include "instantiate_word_level.h"
#include "obligations.h"
#include "property.h"

sequence_matchest instantiate_sequence(
  exprt expr,
  const mp_integer &t,
  const mp_integer &no_timeframes)
{
  if(expr.id() == ID_sva_cycle_delay) // ##[1:2] something
  {
    auto &sva_cycle_delay_expr = to_sva_cycle_delay_expr(expr);
    const auto from = numeric_cast_v<mp_integer>(sva_cycle_delay_expr.from());

    if(sva_cycle_delay_expr.to().is_nil()) // ##1 something
    {
      const auto u = t + from;

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
      mp_integer to;

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

      sequence_matchest matches;

      for(mp_integer u = lower; u <= upper; ++u)
      {
        auto sub_result =
          instantiate_sequence(sva_cycle_delay_expr.op(), u, no_timeframes);
        for(auto &match : sub_result)
          matches.push_back(match);
      }

      return matches;
    }
  }
  else if(expr.id() == ID_sva_sequence_concatenation)
  {
    auto &implication = to_binary_expr(expr);
    sequence_matchest result;

    // This is the product of the match points on the LHS and RHS
    const auto lhs_matches =
      instantiate_sequence(implication.lhs(), t, no_timeframes);

    for(auto &lhs_match : lhs_matches)
    {
      auto t_rhs = lhs_match.end_time;

      // Do we exceed the bound? Make it 'true'
      if(t_rhs >= no_timeframes)
      {
        DATA_INVARIANT(no_timeframes != 0, "must have timeframe");
        return {{no_timeframes - 1, true_exprt()}};
      }

      const auto rhs_matches =
        instantiate_sequence(implication.rhs(), t_rhs, no_timeframes);

      for(auto &rhs_match : rhs_matches)
      {
        auto cond = and_exprt{lhs_match.condition, rhs_match.condition};
        result.push_back({rhs_match.end_time, cond});
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

    const auto lhs_matches =
      instantiate_sequence(intersect.lhs(), t, no_timeframes);
    const auto rhs_matches =
      instantiate_sequence(intersect.rhs(), t, no_timeframes);

    sequence_matchest result;

    for(auto &lhs_match : lhs_matches)
    {
      for(auto &rhs_match : rhs_matches)
      {
        // Same length?
        if(lhs_match.end_time == rhs_match.end_time)
        {
          result.emplace_back(
            lhs_match.end_time,
            and_exprt{lhs_match.condition, rhs_match.condition});
        }
      }
    }

    return result;
  }
  else if(expr.id() == ID_sva_sequence_first_match)
  {
    auto &first_match = to_sva_sequence_first_match_expr(expr);

    const auto lhs_matches =
      instantiate_sequence(first_match.lhs(), t, no_timeframes);

    // the match of seq with the earliest ending clock tick is a
    // match of first_match (seq)
    std::optional<mp_integer> earliest;

    for(auto &match : lhs_matches)
    {
      if(!earliest.has_value() || earliest.value() > match.end_time)
        earliest = match.end_time;
    }

    if(!earliest.has_value())
      return {}; // no match

    sequence_matchest result;

    for(auto &match : lhs_matches)
    {
      // Earliest?
      if(match.end_time == earliest.value())
      {
        result.push_back(match);
      }
    }

    return result;
  }
  else if(expr.id() == ID_sva_sequence_throughout)
  {
    // IEEE 1800-2017 16.9.9
    // exp throughout seq matches along an interval provided
    // - seq matches along the interval and
    // - exp evaluates to true at each clock tick of the interval.
    auto &throughout = to_sva_sequence_throughout_expr(expr);

    const auto rhs_matches =
      instantiate_sequence(throughout.rhs(), t, no_timeframes);

    sequence_matchest result;

    for(auto &rhs_match : rhs_matches)
    {
      exprt::operandst conjuncts = {rhs_match.condition};

      for(mp_integer new_t = t; new_t <= rhs_match.end_time; ++new_t)
      {
        auto obligations =
          property_obligations(throughout.lhs(), new_t, no_timeframes);
        conjuncts.push_back(obligations.conjunction().second);
      }

      result.emplace_back(rhs_match.end_time, conjunction(conjuncts));
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
    auto &and_expr = to_sva_and_expr(expr);
    auto matches_lhs = instantiate_sequence(and_expr.lhs(), t, no_timeframes);
    auto matches_rhs = instantiate_sequence(and_expr.rhs(), t, no_timeframes);

    sequence_matchest result;

    for(auto &match_lhs : matches_lhs)
      for(auto &match_rhs : matches_rhs)
      {
        auto end_time = std::max(match_lhs.end_time, match_rhs.end_time);
        auto cond = and_exprt{match_lhs.condition, match_rhs.condition};
        result.emplace_back(std::move(end_time), std::move(cond));
      }

    return result;
  }
  else if(expr.id() == ID_sva_or)
  {
    // IEEE 1800-2017 16.9.7
    // The set of matches of a or b is the set union of the matches of a
    // and the matches of b.
    sequence_matchest result;

    for(auto &op : expr.operands())
      for(auto &match : instantiate_sequence(op, t, no_timeframes))
        result.push_back(match);

    return result;
  }
  else if(expr.id() == ID_sva_sequence_consecutive_repetition)
  {
    // x[*n] is syntactic sugar for x ##1 ... ##1 x, with n repetitions
    auto &repetition = to_sva_sequence_consecutive_repetition_expr(expr);
    return instantiate_sequence(repetition.lower(), t, no_timeframes);
  }
  else if(
    expr.id() == ID_sva_sequence_repetition_plus ||
    expr.id() == ID_sva_sequence_repetition_star)
  {
    // x[+] and x[*]
    auto &op = to_unary_expr(expr).op();

    // Is x a sequence or a state predicate?
    if(is_SVA_sequence_operator(op))
      PRECONDITION(false); // no support

    sequence_matchest result;

    // we incrementally add conjuncts to the condition
    exprt::operandst conjuncts;

    for(mp_integer u = t; u < no_timeframes; ++u)
    {
      // does x hold in state u?
      auto cond_u = instantiate(op, u, no_timeframes);
      conjuncts.push_back(cond_u);
      result.push_back({u, conjunction(conjuncts)});
    }

    // In addition to the above, x[*] allows an empty match.
    if(expr.id() == ID_sva_sequence_repetition_star)
      result.push_back({t, true_exprt{}});

    return result;
  }
  else
  {
    // not a sequence, evaluate as state predicate
    auto obligations = property_obligations(expr, t, no_timeframes);
    auto conjunction = obligations.conjunction();
    return {{conjunction.first, conjunction.second}};
  }
}
