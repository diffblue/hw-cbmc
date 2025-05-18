/*******************************************************************\

Module: SVA Sequence Matches

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "sva_sequence_match.h"

#include <util/arith_tools.h>
#include <util/std_expr.h>

#include <verilog/sva_expr.h>

sva_sequence_matcht sva_sequence_matcht::true_match(const mp_integer &n)
{
  sva_sequence_matcht result;
  for(mp_integer i; i < n; ++i)
    result.cond_vector.push_back(true_exprt{});
  return result;
}

// nonoverlapping concatenation
sva_sequence_matcht concat(sva_sequence_matcht a, const sva_sequence_matcht &b)
{
  a.cond_vector.insert(
    a.cond_vector.end(), b.cond_vector.begin(), b.cond_vector.end());
  return a;
}

// overlapping concatenation
sva_sequence_matcht
overlapping_concat(sva_sequence_matcht a, sva_sequence_matcht b)
{
  PRECONDITION(!a.empty_match());
  PRECONDITION(!b.empty_match());
  auto a_last = a.cond_vector.back();
  a.cond_vector.pop_back();
  b.cond_vector.front() = conjunction({a_last, b.cond_vector.front()});
  return concat(std::move(a), b);
}

std::vector<sva_sequence_matcht> LTL_sequence_matches(const exprt &sequence)
{
  if(sequence.id() == ID_sva_boolean)
  {
    // atomic proposition
    return {sva_sequence_matcht{to_sva_boolean_expr(sequence).op()}};
  }
  else if(sequence.id() == ID_sva_sequence_concatenation)
  {
    auto &concatenation = to_sva_sequence_concatenation_expr(sequence);
    auto matches_lhs = LTL_sequence_matches(concatenation.lhs());
    auto matches_rhs = LTL_sequence_matches(concatenation.rhs());

    if(matches_lhs.empty() || matches_rhs.empty())
      return {};

    std::vector<sva_sequence_matcht> result;

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
      auto delay_sequence = sva_sequence_matcht::true_match(from_int);

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
      std::vector<sva_sequence_matcht> new_matches;

      for(mp_integer i = from_int; i <= to_int; ++i)
      {
        // delay as instructed
        auto delay_sequence = sva_sequence_matcht::true_match(i);

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
  else if(sequence.id() == ID_sva_and)
  {
    // IEEE 1800-2017 16.9.5
    // 1. Both operands must match.
    // 2. Both sequences start at the same time.
    // 3. The end time of the composite sequence is
    //    the end time of the operand sequence that completes last.
    auto &and_expr = to_sva_and_expr(sequence);
    auto matches_lhs = LTL_sequence_matches(and_expr.lhs());
    auto matches_rhs = LTL_sequence_matches(and_expr.rhs());

    if(matches_lhs.empty() || matches_rhs.empty())
      return {};

    std::vector<sva_sequence_matcht> result;

    for(auto &match_lhs : matches_lhs)
      for(auto &match_rhs : matches_rhs)
      {
        sva_sequence_matcht new_match;
        auto new_length = std::max(match_lhs.length(), match_rhs.length());
        new_match.cond_vector.resize(new_length);
        for(std::size_t i = 0; i < new_length; i++)
        {
          exprt::operandst conjuncts;
          if(i < match_lhs.cond_vector.size())
            conjuncts.push_back(match_lhs.cond_vector[i]);

          if(i < match_rhs.cond_vector.size())
            conjuncts.push_back(match_rhs.cond_vector[i]);

          new_match.cond_vector[i] = conjunction(conjuncts);
        }

        result.push_back(std::move(new_match));
      }

    return result;
  }
  else if(sequence.id() == ID_sva_or)
  {
    // IEEE 1800-2017 16.9.7
    // The set of matches of a or b is the set union of the matches of a
    // and the matches of b.
    std::vector<sva_sequence_matcht> result;

    for(auto &op : to_sva_or_expr(sequence).operands())
    {
      auto op_matches = LTL_sequence_matches(op);
      if(op_matches.empty())
        return {}; // not supported
      for(auto &match : op_matches)
        result.push_back(std::move(match));
    }

    return result;
  }
  else
  {
    return {}; // unsupported
  }
}
