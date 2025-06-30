/*******************************************************************\

Module: Rewrite SVA Sequences

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "rewrite_sva_sequence.h"

#include <util/arith_tools.h>
#include <util/mathematical_types.h>

#include <verilog/sva_expr.h>

#include "temporal_logic.h"

/// 1800-2017 F.4.3
/// Returns true iff the given SVA sequence admits an empty match.
bool admits_empty(const exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_verilog_sva_sequence);
  PRECONDITION(is_SVA_sequence_operator(expr));

  if(expr.id() == ID_sva_boolean)
    return false; // admits_empty(b) = 0
  else if(expr.id() == ID_sva_cycle_delay)
  {
    auto &cycle_delay = to_sva_cycle_delay_expr(expr);

    if(cycle_delay.from().is_zero() && !cycle_delay.is_range())
    {
      // admits_empty((r1 ##0 r2)) = 0
      return false;
    }
    else
    {
      // admits_empty((r1 ##1 r2)) = admits_empty(r1) && admits_empty(r2)
      return cycle_delay.lhs().is_not_nil() &&
             admits_empty(cycle_delay.lhs()) && admits_empty(cycle_delay.rhs());
    }
  }
  else if(expr.id() == ID_sva_cycle_delay_star)
  {
    auto &cycle_delay = to_sva_cycle_delay_star_expr(expr);

    return cycle_delay.lhs().is_not_nil() && admits_empty(cycle_delay.lhs()) &&
           admits_empty(cycle_delay.rhs());
  }
  else if(expr.id() == ID_sva_cycle_delay_plus)
  {
    auto &cycle_delay = to_sva_cycle_delay_plus_expr(expr);

    return cycle_delay.lhs().is_not_nil() && admits_empty(cycle_delay.lhs()) &&
           admits_empty(cycle_delay.rhs());
  }
  else if(expr.id() == ID_sva_or)
  {
    // admits_empty((r1 or r2)) = admits_empty(r1) || admits_empty(r2)
    auto &or_expr = to_sva_or_expr(expr);
    return admits_empty(or_expr.lhs()) || admits_empty(or_expr.rhs());
  }
  else if(expr.id() == ID_sva_sequence_intersect)
  {
    // admits_empty((r1 intersect r2)) = admits_empty(r1) && admits_empty(r2)
    auto &intersect_expr = to_sva_sequence_intersect_expr(expr);
    return admits_empty(intersect_expr.lhs()) &&
           admits_empty(intersect_expr.rhs());
  }
  else if(expr.id() == ID_sva_sequence_first_match)
  {
    // admits_empty(first_match(r)) = admits_empty(r)
    auto &first_match_expr = to_sva_sequence_first_match_expr(expr);
    return admits_empty(first_match_expr.lhs()) &&
           admits_empty(first_match_expr.rhs());
  }
  else if(expr.id() == ID_sva_sequence_repetition_star)
  {
    // admits_empty(r[*0]) = 1
    // admits_empty(r[*1:$]) = admits_empty(r)
    auto &repetition_expr = to_sva_sequence_repetition_star_expr(expr);
    if(repetition_expr.is_range())
    {
      if(repetition_expr.from().is_zero())
        return true;
      else
        return admits_empty(repetition_expr.op());
    }
    else // singleton
    {
      if(repetition_expr.repetitions().is_zero())
        return true;
      else
        return admits_empty(repetition_expr.op());
    }
  }
  else if(
    expr.id() == ID_sva_sequence_goto_repetition ||
    expr.id() == ID_sva_sequence_non_consecutive_repetition)
  {
    return false;
  }
  else
  {
    DATA_INVARIANT(false, "unexpected SVA sequence: " + expr.id_string());
  }
}

exprt rewrite_sva_sequence(exprt expr)
{
  PRECONDITION(expr.type().id() == ID_verilog_sva_sequence);
  PRECONDITION(is_SVA_sequence_operator(expr));

  if(expr.id() == ID_sva_cycle_delay)
  {
    // 1800-2017 16.9.2.1
    // - (empty ##0 seq) does not result in a match.
    // - (seq ##0 empty) does not result in a match.
    // - (empty ##n seq), where n is greater than 0, is equivalent to (##(n-1) seq).
    // - (seq ##n empty), where n is greater than 0, is equivalent to (seq ##(n-1) `true).
    auto &cycle_delay_expr = to_sva_cycle_delay_expr(expr);

    bool lhs_admits_empty = cycle_delay_expr.lhs().is_not_nil() &&
                            admits_empty(cycle_delay_expr.lhs());

    bool rhs_admits_empty = admits_empty(cycle_delay_expr.rhs());

    // apply recursively to operands
    if(cycle_delay_expr.lhs().is_not_nil())
      cycle_delay_expr.lhs() = rewrite_sva_sequence(cycle_delay_expr.lhs());

    cycle_delay_expr.rhs() = rewrite_sva_sequence(cycle_delay_expr.rhs());

    // consider empty match cases
    if(!lhs_admits_empty && !rhs_admits_empty)
      return cycle_delay_expr;

    if(lhs_admits_empty)
    {
      if(cycle_delay_expr.is_range())
      {
        mp_integer from_int =
          numeric_cast_v<mp_integer>(cycle_delay_expr.from());
        DATA_INVARIANT(from_int >= 0, "delay must not be negative");
        abort();
      }
      else // singleton
      {
        mp_integer delay_int =
          numeric_cast_v<mp_integer>(cycle_delay_expr.from());
        DATA_INVARIANT(delay_int >= 0, "delay must not be negative");

        // lhs ##0 rhs
        if(delay_int == 0)
          return cycle_delay_expr;
        else
        {
          // (empty ##n seq), where n is greater than 0, is equivalent to (##(n-1) seq).
          auto delay =
            from_integer(delay_int - 1, cycle_delay_expr.from().type());
          auto empty_match_case =
            sva_cycle_delay_exprt{delay, cycle_delay_expr.rhs()};
          return sva_or_exprt{empty_match_case, cycle_delay_expr, expr.type()};
        }
      }
    }
    else if(rhs_admits_empty)
    {
      if(cycle_delay_expr.is_range())
      {
        mp_integer from_int =
          numeric_cast_v<mp_integer>(cycle_delay_expr.from());
        DATA_INVARIANT(from_int >= 0, "delay must not be negative");
        abort();
      }
      else // singleton
      {
        mp_integer delay_int =
          numeric_cast_v<mp_integer>(cycle_delay_expr.from());
        DATA_INVARIANT(delay_int >= 0, "delay must not be negative");

        // lhs ##0 rhs
        if(delay_int == 0)
          return cycle_delay_expr;
        else
        {
          // (seq ##n empty), where n is greater than 0, is equivalent to (seq ##(n-1) `true).
          auto delay =
            from_integer(delay_int - 1, cycle_delay_expr.from().type());
          auto empty_match_case = sva_cycle_delay_exprt{
            cycle_delay_expr.lhs(),
            delay,
            nil_exprt{},
            sva_boolean_exprt{true_exprt{}, expr.type()}};
          return sva_or_exprt{empty_match_case, cycle_delay_expr, expr.type()};
        }
      }
    }
    else // neither lhs nor rhs admit an empty match
      return cycle_delay_expr;
  }
  else if(expr.id() == ID_sva_sequence_repetition_star)
  {
    auto &repetition_expr = to_sva_sequence_repetition_star_expr(expr);
    repetition_expr.op() = rewrite_sva_sequence(repetition_expr.op());

    if(repetition_expr.is_empty_match())
    {
      // Empty match. Leave as is. Now denotes "no match".
    }
    else if(!repetition_expr.repetitions_given())
    {
      // f [*] g    ---> f [*1:$] g
      repetition_expr = sva_sequence_repetition_star_exprt{
        repetition_expr.op(),
        from_integer(1, integer_typet{}),
        infinity_exprt{integer_typet{}}};
    }
    else if(repetition_expr.is_range() && repetition_expr.from().is_zero())
    {
      // f [*0:x] g ---> f [*1:x] g
      repetition_expr.from() = from_integer(1, repetition_expr.from().type());
    }

    return repetition_expr;
  }
  else if(expr.id() == ID_sva_sequence_repetition_plus)
  {
    auto &repetition_expr = to_sva_sequence_repetition_plus_expr(expr);
    repetition_expr.op() = rewrite_sva_sequence(repetition_expr.op());
    return repetition_expr;
  }
  else if(
    expr.id() == ID_sva_or || expr.id() == ID_sva_and ||
    expr.id() == ID_sva_sequence_intersect ||
    expr.id() == ID_sva_sequence_within)
  {
    // All operands are sequences
    for(auto &op : expr.operands())
      op = rewrite_sva_sequence(op);
    return expr;
  }
  else if(expr.id() == ID_sva_sequence_first_match)
  {
    auto &first_match = to_sva_sequence_first_match_expr(expr);
    first_match.sequence() = rewrite_sva_sequence(first_match.sequence());
    return first_match;
  }
  else if(expr.id() == ID_sva_cycle_delay_star)
  {
    auto &cycle_delay = to_sva_cycle_delay_star_expr(expr);
    if(cycle_delay.lhs().is_not_nil())
      cycle_delay.lhs() = rewrite_sva_sequence(cycle_delay.lhs());
    cycle_delay.rhs() = rewrite_sva_sequence(cycle_delay.rhs());
    return expr;
  }
  else if(expr.id() == ID_sva_cycle_delay_plus)
  {
    auto &cycle_delay = to_sva_cycle_delay_plus_expr(expr);
    if(cycle_delay.lhs().is_not_nil())
      cycle_delay.lhs() = rewrite_sva_sequence(cycle_delay.lhs());
    cycle_delay.rhs() = rewrite_sva_sequence(cycle_delay.rhs());
    return expr;
  }
  else if(expr.id() == ID_sva_sequence_throughout)
  {
    auto &throughout = to_sva_sequence_throughout_expr(expr);
    throughout.sequence() = rewrite_sva_sequence(throughout.sequence());
    return expr;
  }
  else if(
    expr.id() == ID_sva_sequence_goto_repetition ||
    expr.id() == ID_sva_sequence_non_consecutive_repetition)
  {
    // these take a Boolean as argument, not a sequence
    return expr;
  }
  else if(expr.id() == ID_sva_boolean)
  {
    return expr;
  }
  else
  {
    DATA_INVARIANT(false, "unexpected SVA sequence: " + expr.id_string());
  }
}
