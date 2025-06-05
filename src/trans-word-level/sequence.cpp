/*******************************************************************\

Module: Encoding SVA sequences

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "sequence.h"

#include <util/arith_tools.h>
#include <util/mathematical_types.h>

#include <ebmc/ebmc_error.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

#include "instantiate_word_level.h"
#include "obligations.h"
#include "property.h"

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

sequence_matchest instantiate_sequence(
  exprt expr,
  sva_sequence_semanticst semantics,
  const mp_integer &t,
  const mp_integer &no_timeframes)
{
  if(expr.id() == ID_sva_cycle_delay) // ##[1:2] something
  {
    auto &sva_cycle_delay_expr = to_sva_cycle_delay_expr(expr);
    const auto from = numeric_cast_v<mp_integer>(sva_cycle_delay_expr.from());

    if(!sva_cycle_delay_expr.is_range()) // ##1 something
    {
      const auto u = t + from;

      // Do we exceed the bound? Make it 'false'/'true', depending
      // on semantics.
      if(u >= no_timeframes)
      {
        DATA_INVARIANT(no_timeframes != 0, "must have timeframe");
        if(semantics == sva_sequence_semanticst::WEAK)
          return {{no_timeframes - 1, true_exprt{}}};
        else         // STRONG
          return {}; // no match
      }
      else
        return instantiate_sequence(
          sva_cycle_delay_expr.op(), semantics, u, no_timeframes);
    }
    else // ##[from:to] something
    {
      auto lower = t + from;
      mp_integer upper;

      if(sva_cycle_delay_expr.is_unbounded())
      {
        DATA_INVARIANT(no_timeframes != 0, "must have timeframe");
        upper = no_timeframes;
      }
      else
      {
        auto to = numeric_cast_v<mp_integer>(sva_cycle_delay_expr.to());
        upper = t + to;
      }

      sequence_matchest matches;

      // Do we exceed the bound? Add an unconditional match when using
      // weak semantics.
      if(upper >= no_timeframes)
      {
        upper = no_timeframes - 1;

        if(semantics == sva_sequence_semanticst::WEAK)
        {
          DATA_INVARIANT(no_timeframes != 0, "must have timeframe");
          matches.emplace_back(no_timeframes - 1, true_exprt());
        }
      }

      // Add a potential match for each timeframe in the range
      for(mp_integer u = lower; u <= upper; ++u)
      {
        auto sub_result = instantiate_sequence(
          sva_cycle_delay_expr.op(), semantics, u, no_timeframes);
        for(auto &match : sub_result)
          matches.push_back(match);
      }

      return matches;
    }
  }
  else if(expr.id() == ID_sva_cycle_delay_star) // ##[*] something
  {
    auto &cycle_delay_star = to_sva_cycle_delay_star_expr(expr);
    return instantiate_sequence(
      cycle_delay_star.lower(), semantics, t, no_timeframes);
  }
  else if(expr.id() == ID_sva_cycle_delay_plus) // ##[+] something
  {
    auto &cycle_delay_plus = to_sva_cycle_delay_plus_expr(expr);
    return instantiate_sequence(
      cycle_delay_plus.lower(), semantics, t, no_timeframes);
  }
  else if(expr.id() == ID_sva_sequence_concatenation)
  {
    auto &implication = to_binary_expr(expr);
    sequence_matchest result;

    // This is the product of the match points on the LHS and RHS
    const auto lhs_matches =
      instantiate_sequence(implication.lhs(), semantics, t, no_timeframes);

    for(auto &lhs_match : lhs_matches)
    {
      auto t_rhs = lhs_match.end_time;

      // Do we exceed the bound? Make it 'false'/'true', depending
      // on semantics.
      if(t_rhs >= no_timeframes)
      {
        DATA_INVARIANT(no_timeframes != 0, "must have timeframe");
        if(semantics == sva_sequence_semanticst::WEAK)
          return {{no_timeframes - 1, true_exprt{}}};
        else         // STRONG
          return {}; // no match
      }

      const auto rhs_matches = instantiate_sequence(
        implication.rhs(), semantics, t_rhs, no_timeframes);

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
      instantiate_sequence(intersect.lhs(), semantics, t, no_timeframes);
    const auto rhs_matches =
      instantiate_sequence(intersect.rhs(), semantics, t, no_timeframes);

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
      instantiate_sequence(first_match.lhs(), semantics, t, no_timeframes);

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
      instantiate_sequence(throughout.rhs(), semantics, t, no_timeframes);

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
    // If the lhs match is contained anywhere within the rhs match,
    // then return the rhs match.

    auto &within_expr = to_sva_sequence_within_expr(expr);
    const auto matches_rhs =
      instantiate_sequence(within_expr.rhs(), semantics, t, no_timeframes);

    sequence_matchest result;

    for(auto &match_rhs : matches_rhs)
    {
      for(auto start_lhs = t; start_lhs <= match_rhs.end_time; ++start_lhs)
      {
        auto matches_lhs = instantiate_sequence(
          within_expr.lhs(), semantics, start_lhs, no_timeframes);

        for(auto &match_lhs : matches_lhs)
        {
          // The end_time of the lhs match must be no later than the
          // end_time of the rhs match.
          if(match_lhs.end_time <= match_rhs.end_time)
          {
            // return the rhs end_time
            auto cond = and_exprt{match_lhs.condition, match_rhs.condition};
            result.emplace_back(match_rhs.end_time, std::move(cond));
          }
        }
      }
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
      instantiate_sequence(and_expr.lhs(), semantics, t, no_timeframes);
    auto matches_rhs =
      instantiate_sequence(and_expr.rhs(), semantics, t, no_timeframes);

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
      for(auto &match : instantiate_sequence(op, semantics, t, no_timeframes))
        result.push_back(match);

    return result;
  }
  else if(expr.id() == ID_sva_sequence_repetition_star) // [*...]
  {
    auto &repetition = to_sva_sequence_repetition_star_expr(expr);
    if(repetition.is_empty_match())
    {
      // [*0] denotes the empty match
      return {sequence_matcht::empty_match(t)};
    }
    else if(repetition.is_unbounded() && repetition.repetitions_given())
    {
      // [*from:$] -> op[*from:to]
      // with to = no_timeframes - t
      auto to = from_integer(no_timeframes - t, integer_typet{});
      auto new_repetition = sva_sequence_repetition_star_exprt{
        repetition.op(), repetition.from(), to};

      return instantiate_sequence(
        new_repetition.lower(), semantics, t, no_timeframes);
    }
    else
    {
      // [*], [*n], [*x:y]
      return instantiate_sequence(
        repetition.lower(), semantics, t, no_timeframes);
    }
  }
  else if(expr.id() == ID_sva_sequence_repetition_plus) // [+]
  {
    auto &repetition = to_sva_sequence_repetition_plus_expr(expr);
    return instantiate_sequence(
      repetition.lower(), semantics, t, no_timeframes);
  }
  else if(expr.id() == ID_sva_sequence_goto_repetition) // [->...]
  {
    auto &repetition = to_sva_sequence_goto_repetition_expr(expr);
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
      result.emplace_back(u, sequence_count_condition(repetition, matches));
    }

    return result;
  }
  else if(expr.id() == ID_sva_sequence_non_consecutive_repetition) // [=...]
  {
    auto &repetition = to_sva_sequence_non_consecutive_repetition_expr(expr);
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

      // We have a match for op[=n] if matches is n.
      result.emplace_back(u, sequence_count_condition(repetition, matches));
    }

    return result;
  }
  else if(expr.id() == ID_sva_boolean)
  {
    // a state predicate
    auto &predicate = to_sva_boolean_expr(expr).op();
    auto instantiated = instantiate_property(predicate, t, no_timeframes);
    return {{t, instantiated}};
  }
  else
  {
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      false, "unexpected sequence expression", expr.pretty());
  }
}
