/*******************************************************************\

Module: Encoding SVA sequences

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "sequence.h"

#include <util/arith_tools.h>
#include <util/mathematical_types.h>

#include <ebmc/ebmc_error.h>
#include <temporal-logic/rewrite_sva_sequence.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

#include "instantiate_word_level.h"
#include "obligations.h"

// true iff there is a pending match in the given set
static bool has_pending(const sequence_matchest &matches)
{
  for(auto &m : matches)
    if(m.is_pending())
      return true;
  return false;
}

// condition on counters for ocurrences of non-consecutive repetitions
exprt sequence_count_condition(
  const sva_sequence_repetition_exprt &expr,
  const exprt &counter)
{
  if(expr.is_range())
  {
    // number of repetitions inside a range
    auto from = numeric_cast_v<mp_integer>(expr.from());

    if(expr.is_unbounded())
    {
      return binary_relation_exprt{
        counter, ID_ge, from_integer(from, counter.type())};
    }
    else
    {
      auto to = numeric_cast_v<mp_integer>(expr.to());

      return and_exprt{
        binary_relation_exprt{
          counter, ID_ge, from_integer(from, counter.type())},
        binary_relation_exprt{
          counter, ID_le, from_integer(to, counter.type())}};
    }
  }
  else
  {
    // fixed number of repetitions
    auto repetitions = numeric_cast_v<mp_integer>(expr.repetitions());
    return equal_exprt{counter, from_integer(repetitions, counter.type())};
  }
}

/// determine type for the repetition counter
typet sequence_count_type(
  const sva_sequence_repetition_exprt &expr,
  const mp_integer &no_timeframes)
{
  mp_integer max;

  if(expr.is_range())
  {
    if(expr.is_unbounded())
      max = numeric_cast_v<mp_integer>(expr.from());
    else
      max = numeric_cast_v<mp_integer>(expr.to());
  }
  else
    max = numeric_cast_v<mp_integer>(expr.repetitions());

  max = std::max(no_timeframes, max);

  auto bits = address_bits(max + 1);
  return unsignedbv_typet{bits};
}

sequence_matchest instantiate_sequence_rec(
  exprt expr,
  const mp_integer &t,
  const mp_integer &no_timeframes)
{
  PRECONDITION(t < no_timeframes);

  if(expr.id() == ID_sva_cycle_delay) // ##[1:2] something
  {
    auto &sva_cycle_delay_expr = to_sva_cycle_delay_expr(expr);

    // This is the product of the match points on the LHS and RHS,
    // with appropriate delay in between.
    sequence_matchest lhs_matches;

    if(sva_cycle_delay_expr.lhs().is_nil())
    {
      // defaults to a length-1 match with condition 'true'
      lhs_matches = {{t, true_exprt{}}};
    }
    else
    {
      lhs_matches =
        instantiate_sequence_rec(sva_cycle_delay_expr.lhs(), t, no_timeframes);
    }

    sequence_matchest result;

    for(auto &lhs_match : lhs_matches)
    {
      if(lhs_match.empty_match())
        continue; // handled by rewrite_sva_sequence

      // A pending match represents a sequence that may complete beyond
      // the bound. Propagate without evaluating the RHS.
      if(lhs_match.is_pending())
      {
        result.push_back(lhs_match);
        continue;
      }

      // now delay
      const auto from = numeric_cast_v<mp_integer>(sva_cycle_delay_expr.from());
      DATA_INVARIANT(from >= 0, "##n must not be negative");

      auto t_rhs_from = lhs_match.end_time() + from;
      mp_integer t_rhs_to;

      if(!sva_cycle_delay_expr.is_range()) // ##1 something
      {
        t_rhs_to = t_rhs_from;
      }
      else if(sva_cycle_delay_expr.is_unbounded()) // ##[from:$] something
      {
        // one beyond the bound
        t_rhs_to = no_timeframes;
      }
      else // ##[from:to] something
      {
        auto to = numeric_cast_v<mp_integer>(sva_cycle_delay_expr.to());
        DATA_INVARIANT(to >= from, "##[a:b] must have a<=b");
        t_rhs_to = lhs_match.end_time() + to;
      }

      // Add a potential match for each timeframe in the range
      for(mp_integer t_rhs = t_rhs_from; t_rhs <= t_rhs_to; ++t_rhs)
      {
        // Do we exceed the bound?
        if(t_rhs >= no_timeframes)
        {
          result.push_back(
            sequence_matcht::pending_match(lhs_match.condition()));
        }
        else // still inside bound
        {
          const auto rhs_matches = instantiate_sequence_rec(
            sva_cycle_delay_expr.rhs(), t_rhs, no_timeframes);

          for(auto &rhs_match : rhs_matches)
          {
            // empty matches are handled by rewrite_sva_sequence
            if(!rhs_match.empty_match())
            {
              auto cond =
                and_exprt{lhs_match.condition(), rhs_match.condition()};
              if(rhs_match.is_pending())
              {
                result.push_back(
                  sequence_matcht::pending_match(std::move(cond)));
              }
              else
                result.emplace_back(rhs_match.end_time(), std::move(cond));
            }
          }
        }
      }
    }

    return result;
  }
  else if(expr.id() == ID_sva_cycle_delay_star) // ##[*] something
  {
    auto &cycle_delay_star = to_sva_cycle_delay_star_expr(expr);
    return instantiate_sequence_rec(cycle_delay_star.lower(), t, no_timeframes);
  }
  else if(expr.id() == ID_sva_cycle_delay_plus) // ##[+] something
  {
    auto &cycle_delay_plus = to_sva_cycle_delay_plus_expr(expr);
    return instantiate_sequence_rec(cycle_delay_plus.lower(), t, no_timeframes);
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
      instantiate_sequence_rec(intersect.lhs(), t, no_timeframes);
    const auto rhs_matches =
      instantiate_sequence_rec(intersect.rhs(), t, no_timeframes);

    sequence_matchest result;

    exprt::operandst concrete_match_conditions;

    for(auto &lhs_match : lhs_matches)
    {
      for(auto &rhs_match : rhs_matches)
      {
        if(!lhs_match.is_pending() && !rhs_match.is_pending())
        {
          // Same length?
          if(lhs_match.end_time() == rhs_match.end_time())
          {
            auto cond = and_exprt{lhs_match.condition(), rhs_match.condition()};
            concrete_match_conditions.push_back(cond);
            result.emplace_back(lhs_match.end_time(), std::move(cond));
          }
        }
      }
    }

    // If either operand has a pending match, the intersect might
    // still match beyond the bound. The pending condition is:
    // no concrete match has fired.
    if(has_pending(lhs_matches) || has_pending(rhs_matches))
    {
      auto no_concrete = concrete_match_conditions.empty()
                           ? static_cast<exprt>(true_exprt{})
                           : not_exprt{disjunction(concrete_match_conditions)};
      result.push_back(sequence_matcht::pending_match(no_concrete));
    }

    return result;
  }
  else if(expr.id() == ID_sva_sequence_first_match)
  {
    auto &first_match = to_sva_sequence_first_match_expr(expr);

    const auto matches =
      instantiate_sequence_rec(first_match.sequence(), t, no_timeframes);

    // first_match(seq): the match of seq with the earliest ending
    // clock tick. In the symbolic setting, we must encode that a
    // match at time t fires only if no earlier match has fired.
    sequence_matchest result;

    // Collect concrete matches sorted by end_time (they already are).
    // Build an "no earlier match" guard for each match point.
    exprt no_earlier_match = true_exprt{};

    // Group by end_time and process in order.
    std::map<mp_integer, exprt::operandst> by_time;
    for(auto &match : matches)
    {
      if(!match.is_pending())
        by_time[match.end_time()].push_back(match.condition());
    }

    for(auto &[end_time, conditions] : by_time)
    {
      auto any_match_here = disjunction(conditions);
      auto guarded = and_exprt{no_earlier_match, any_match_here};
      result.emplace_back(end_time, std::move(guarded));
      // For the next time point, add the condition that no match
      // fired at this time point or earlier.
      no_earlier_match = and_exprt{no_earlier_match, not_exprt{any_match_here}};
    }

    // Propagate pending matches, guarded by no concrete match firing.
    for(auto &match : matches)
    {
      if(match.is_pending())
      {
        result.push_back(sequence_matcht::pending_match(
          and_exprt{no_earlier_match, match.condition()}));
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

    const auto matches =
      instantiate_sequence_rec(throughout.sequence(), t, no_timeframes);

    sequence_matchest result;

    for(auto &match : matches)
    {
      if(match.is_pending())
      {
        // Propagate pending status.
        result.push_back(match);
        continue;
      }

      exprt::operandst conjuncts = {match.condition()};

      for(mp_integer new_t = t; new_t <= match.end_time(); ++new_t)
      {
        auto lhs_inst =
          instantiate_state_predicate(throughout.lhs(), new_t, no_timeframes);
        conjuncts.push_back(lhs_inst);
      }

      result.emplace_back(match.end_time(), conjunction(conjuncts));
    }

    return result;
  }
  else if(expr.id() == ID_sva_sequence_within)
  {
    // If the lhs match is contained anywhere within the rhs match,
    // then return the rhs match.

    auto &within_expr = to_sva_sequence_within_expr(expr);
    const auto matches_rhs =
      instantiate_sequence_rec(within_expr.rhs(), t, no_timeframes);

    sequence_matchest result;
    bool has_pending = false;
    exprt::operandst concrete_match_conditions;

    for(auto &match_rhs : matches_rhs)
    {
      if(match_rhs.is_pending())
      {
        has_pending = true;
        continue;
      }

      for(auto start_lhs = t; start_lhs <= match_rhs.end_time(); ++start_lhs)
      {
        auto matches_lhs =
          instantiate_sequence_rec(within_expr.lhs(), start_lhs, no_timeframes);

        for(auto &match_lhs : matches_lhs)
        {
          if(match_lhs.is_pending())
          {
            has_pending = true;
            continue;
          }

          // The end_time of the lhs match must be no later than the
          // end_time of the rhs match.
          if(match_lhs.end_time() <= match_rhs.end_time())
          {
            // return the rhs end_time
            auto cond = and_exprt{match_lhs.condition(), match_rhs.condition()};
            concrete_match_conditions.push_back(cond);
            result.emplace_back(match_rhs.end_time(), std::move(cond));
          }
        }
      }
    }

    // If either operand has a pending match, 'within' might
    // still match beyond the bound.
    if(has_pending)
    {
      auto no_concrete = concrete_match_conditions.empty()
                           ? static_cast<exprt>(true_exprt{})
                           : not_exprt{disjunction(concrete_match_conditions)};
      result.push_back(sequence_matcht::pending_match(no_concrete));
    }

    return result;
  }
  else if(expr.id() == ID_sva_and)
  {
    // IEEE 1800-2017 16.9.5
    // 1. Both operands must match.
    // 2. Both sequences start at the same time.
    // 3. The end time of the composite sequence is
    //    the end time of the operand sequence that completes last.
    auto &and_expr = to_sva_and_expr(expr);
    auto matches_lhs =
      instantiate_sequence_rec(and_expr.lhs(), t, no_timeframes);
    auto matches_rhs =
      instantiate_sequence_rec(and_expr.rhs(), t, no_timeframes);

    sequence_matchest result;
    exprt::operandst concrete_match_conditions;

    for(auto &match_lhs : matches_lhs)
      for(auto &match_rhs : matches_rhs)
      {
        if(!match_lhs.is_pending() && !match_rhs.is_pending())
        {
          auto end_time = std::max(match_lhs.end_time(), match_rhs.end_time());
          auto cond = and_exprt{match_lhs.condition(), match_rhs.condition()};
          concrete_match_conditions.push_back(cond);
          result.emplace_back(std::move(end_time), std::move(cond));
        }
      }

    // If either operand has a pending match, the 'and' might
    // still match beyond the bound. The pending condition is:
    // no concrete match has fired.
    if(has_pending(matches_lhs) || has_pending(matches_rhs))
    {
      auto no_concrete = concrete_match_conditions.empty()
                           ? static_cast<exprt>(true_exprt{})
                           : not_exprt{disjunction(concrete_match_conditions)};
      result.push_back(sequence_matcht::pending_match(no_concrete));
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
      for(auto &match : instantiate_sequence_rec(op, t, no_timeframes))
      {
        result.push_back(match);
      }

    return result;
  }
  else if(expr.id() == ID_sva_sequence_repetition_star) // [*...]
  {
    auto &repetition = to_sva_sequence_repetition_star_expr(expr);
    if(repetition.is_empty_match())
    {
      // [*0] denotes the empty match.
      return {sequence_matcht::empty_match(t)};
    }
    else if(repetition.is_unbounded() && repetition.repetitions_given())
    {
      // op[*from:$] -> op[*from:to]
      // with to = no_timeframes - t
      auto to = from_integer(no_timeframes - t, integer_typet{});
      auto new_repetition = sva_sequence_repetition_star_exprt{
        repetition.op(), repetition.from(), to};

      return instantiate_sequence_rec(new_repetition.lower(), t, no_timeframes);
    }
    else
    {
      // [*], [*n], [*x:y]
      return instantiate_sequence_rec(repetition.lower(), t, no_timeframes);
    }
  }
  else if(expr.id() == ID_sva_sequence_repetition_plus) // [+]
  {
    auto &repetition = to_sva_sequence_repetition_plus_expr(expr);
    return instantiate_sequence_rec(repetition.lower(), t, no_timeframes);
  }
  else if(
    expr.id() == ID_sva_sequence_goto_repetition ||          // [->...]
    expr.id() == ID_sva_sequence_non_consecutive_repetition) // [=...]
  {
    auto &repetition = to_sva_sequence_repetition_expr(expr);
    auto &condition = repetition.op();

    sequence_matchest result;

    // We add up the number of matches of 'op' starting from
    // timeframe u, until the end of our unwinding.
    const auto type = sequence_count_type(repetition, no_timeframes);
    const auto zero = from_integer(0, type);
    const auto one = from_integer(1, type);
    exprt matches = zero;

    for(mp_integer u = t; u < no_timeframes; ++u)
    {
      // match of op in timeframe u?
      auto rec_op = instantiate(condition, u, no_timeframes);

      // add up
      matches = plus_exprt{matches, if_exprt{rec_op, one, zero}};

      // We have a match for op[->n] if there is a match in timeframe
      // u and matches is n.
      // We have a match for op[=n] if matches is n.
      auto count_cond = sequence_count_condition(repetition, matches);
      if(expr.id() == ID_sva_sequence_goto_repetition)
        result.emplace_back(u, and_exprt{rec_op, count_cond});
      else
        result.emplace_back(u, count_cond);
    }

    // Weak semantics: the sequence could still complete beyond the
    // bound. Add a pending match when the count hasn't yet reached
    // the required minimum.
    auto min = repetition.is_range()
                 ? numeric_cast_v<mp_integer>(repetition.from())
                 : numeric_cast_v<mp_integer>(repetition.repetitions());
    result.push_back(sequence_matcht::pending_match(binary_relation_exprt{
      matches, ID_lt, from_integer(min, matches.type())}));

    return result;
  }
  else if(expr.id() == ID_sva_boolean)
  {
    // a state predicate
    auto &predicate = to_sva_boolean_expr(expr).op();
    auto instantiated =
      instantiate_state_predicate(predicate, t, no_timeframes);
    return {{t, instantiated}};
  }
  else
  {
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      false, "unexpected sequence expression", expr.pretty());
  }
}

sequence_matchest instantiate_sequence(
  exprt expr,
  const mp_integer &t,
  const mp_integer &no_timeframes)
{
  auto rewritten = rewrite_sva_sequence(expr);
  return instantiate_sequence_rec(rewritten, t, no_timeframes);
}
