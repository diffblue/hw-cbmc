/*******************************************************************\

Module: SVA Sequence Matches

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "sva_sequence_match.h"

#include <util/arith_tools.h>
#include <util/std_expr.h>

#include <verilog/sva_expr.h>

#include "rewrite_sva_sequence.h"

sva_sequence_matcht sva_sequence_matcht::true_match(const mp_integer &n)
{
  auto n_size_t = numeric_cast_v<std::size_t>(n);
  return sva_sequence_matcht{std::vector<exprt>(n_size_t, true_exprt{})};
}

// nonoverlapping concatenation
sva_sequence_matcht concat(sva_sequence_matcht a, const sva_sequence_matcht &b)
{
  a.cond_vector.insert(
    a.cond_vector.end(), b.cond_vector.begin(), b.cond_vector.end());
  return a;
}

// nonoverlapping concatenation
sva_sequence_matcht repeat(sva_sequence_matcht m, const mp_integer &n)
{
  std::vector<exprt> cond_vector;
  cond_vector.reserve(numeric_cast_v<std::size_t>(n * m.length()));
  for(mp_integer i = 0; i < n; ++i)
    cond_vector.insert(
      cond_vector.end(), m.cond_vector.begin(), m.cond_vector.end());
  return sva_sequence_matcht{std::move(cond_vector)};
}

// overlapping concatenation
sva_sequence_matcht
overlapping_concat(sva_sequence_matcht a, sva_sequence_matcht b)
{
  PRECONDITION(!a.empty_match());
  PRECONDITION(!b.empty_match());
  auto a_last = a.cond_vector.back();
  a.cond_vector.pop_back();
  if(!a_last.is_true())
    b.cond_vector.front() = conjunction({a_last, b.cond_vector.front()});
  return concat(std::move(a), b);
}

std::vector<sva_sequence_matcht> sva_sequence_matches_rec(const exprt &sequence)
{
  if(sequence.id() == ID_sva_boolean)
  {
    // atomic proposition
    return {sva_sequence_matcht{to_sva_boolean_expr(sequence).op()}};
  }
  else if(sequence.id() == ID_sva_sequence_repetition_star) // [*n], [*n:m]
  {
    auto &repetition = to_sva_sequence_repetition_star_expr(sequence);
    auto matches_op = sva_sequence_matches_rec(repetition.op());

    std::vector<sva_sequence_matcht> result;

    if(repetition.repetitions_given())
    {
      if(repetition.is_range())
      {
        if(repetition.is_unbounded()) // [*n:$]
        {
          throw sva_sequence_match_unsupportedt{sequence}; // no support
        }
        else // [*n:m]
        {
          auto from = numeric_cast_v<mp_integer>(repetition.from());
          auto to = numeric_cast_v<mp_integer>(repetition.to());

          for(mp_integer n = from; n < to; ++n)
            for(auto &match_op : matches_op)
              result.push_back(repeat(match_op, n));
        }
      }
      else // [*n]
      {
        auto n = numeric_cast_v<mp_integer>(repetition.repetitions());

        for(auto &match_op : matches_op)
          result.push_back(repeat(match_op, n));
      }
    }
    else         // [*]
      throw sva_sequence_match_unsupportedt{sequence}; // no support

    return result;
  }
  else if(sequence.id() == ID_sva_cycle_delay)
  {
    auto &delay = to_sva_cycle_delay_expr(sequence);

    // These have an optional LHS and a RHS.
    std::vector<sva_sequence_matcht> lhs_matches;

    if(delay.lhs().is_nil())
    {
      // If the LHS is not given, it's equivalent to 'true'.
      lhs_matches = {sva_sequence_matcht::true_match(1)};
    }
    else
    {
      lhs_matches = LTL_sequence_matches(delay.lhs());
    }

    // The delay in between lhs and rhs
    std::vector<sva_sequence_matcht> delay_matches;

    auto from_int = numeric_cast_v<mp_integer>(delay.from());

    if(!delay.is_range()) // f ##n g
    {
      delay_matches = {sva_sequence_matcht::true_match(from_int)};
    }
    else if(delay.is_unbounded()) // f ##[from:$] g
    {
      throw sva_sequence_match_unsupportedt{sequence}; // can't encode
    }
    else // f ##[from:to] g
    {
      auto to_int = numeric_cast_v<mp_integer>(delay.to());

      for(mp_integer i = from_int; i <= to_int; ++i)
        delay_matches.push_back(sva_sequence_matcht::true_match(i));
    }

    // now do RHS
    auto rhs_matches = LTL_sequence_matches(delay.rhs());

    // cross product lhs x delay x rhs
    std::vector<sva_sequence_matcht> result;

    for(auto &lhs_match : lhs_matches)
      for(auto &delay_match : delay_matches)
        for(auto &rhs_match : rhs_matches)
        {
          // Drop empty matches, taken care of by rewrite_sva_sequence
          if(lhs_match.empty_match() || rhs_match.empty_match())
            continue;

          // Sequence concatenation is overlapping
          auto new_match =
            overlapping_concat(lhs_match, concat(delay_match, rhs_match));
          CHECK_RETURN(
            new_match.length() ==
            lhs_match.length() + delay_match.length() + rhs_match.length() - 1);
          result.push_back(std::move(new_match));
        }

    return result;
  }
  else if(sequence.id() == ID_sva_and)
  {
    // IEEE 1800-2017 16.9.5
    // 1. Both operands must match.
    // 2. Both sequences start at the same time.
    // 3. The end time of the composite sequence is
    //    the end time of the operand sequence that completes last.
    auto &and_expr = to_sva_and_expr(sequence);
    auto matches_lhs = sva_sequence_matches_rec(and_expr.lhs());
    auto matches_rhs = sva_sequence_matches_rec(and_expr.rhs());

    std::vector<sva_sequence_matcht> result;

    for(auto &match_lhs : matches_lhs)
      for(auto &match_rhs : matches_rhs)
      {
        std::vector<exprt> cond_vector;
        auto new_length = std::max(match_lhs.length(), match_rhs.length());
        cond_vector.resize(new_length);
        for(std::size_t i = 0; i < new_length; i++)
        {
          exprt::operandst conjuncts;
          if(i < match_lhs.cond_vector.size())
            conjuncts.push_back(match_lhs.cond_vector[i]);

          if(i < match_rhs.cond_vector.size())
            conjuncts.push_back(match_rhs.cond_vector[i]);

          cond_vector[i] = conjunction(conjuncts);
        }

        result.emplace_back(std::move(cond_vector));
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
      auto op_matches = sva_sequence_matches_rec(op);
      if(op_matches.empty())
        throw sva_sequence_match_unsupportedt{sequence}; // not supported
      for(auto &match : op_matches)
        result.push_back(std::move(match));
    }

    return result;
  }
  else
  {
    throw sva_sequence_match_unsupportedt{sequence}; // not supported
  }
}

std::vector<sva_sequence_matcht> LTL_sequence_matches(const exprt &sequence)
{
  // rewrite, then do recursion
  auto rewritten = rewrite_sva_sequence(sequence);
  return sva_sequence_matches_rec(rewritten);
}
