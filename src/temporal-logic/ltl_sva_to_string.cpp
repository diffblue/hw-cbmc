/*******************************************************************\

Module: Property Instrumentation via Buechi Automata

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "ltl_sva_to_string.h"

#include <util/arith_tools.h>
#include <util/string2int.h>

#include <ebmc/ebmc_error.h>
#include <verilog/sva_expr.h>

#include "ltl.h"
#include "temporal_expr.h"
#include "temporal_logic.h"

// https://spot.lre.epita.fr/tl.pdf

exprt ltl_sva_to_stringt::atom(const std::string &string) const
{
  // map back to number
  auto number = safe_string2size_t(string);

  PRECONDITION(number < atoms.size());

  return atoms[number];
}

ltl_sva_to_stringt::resultt
ltl_sva_to_stringt::suffix(std::string s, const unary_exprt &expr, modet mode)
{
  auto op_rec = rec(expr.op(), mode);

  if(op_rec.p == precedencet::ATOM || op_rec.p == precedencet::SUFFIX)
    return resultt{precedencet::SUFFIX, op_rec.s + s};
  else
    return resultt{precedencet::SUFFIX, '(' + op_rec.s + ')' + s};
}

ltl_sva_to_stringt::resultt
ltl_sva_to_stringt::prefix(std::string s, const unary_exprt &expr, modet mode)
{
  auto op_rec = rec(expr.op(), mode);

  if(op_rec.p == precedencet::ATOM || op_rec.p == precedencet::PREFIX)
    return resultt{precedencet::PREFIX, s + op_rec.s};
  else
    return resultt{precedencet::PREFIX, s + '(' + op_rec.s + ')'};
}

ltl_sva_to_stringt::resultt
ltl_sva_to_stringt::infix(std::string s, const exprt &expr, modet mode)
{
  std::string result;
  bool first = true;

  for(auto &op : expr.operands())
  {
    if(first)
      first = false;
    else
      result += s;

    auto op_rec = rec(op, mode);

    if(op_rec.p == precedencet::ATOM)
      result += op_rec.s;
    else
      result += '(' + op_rec.s + ')';
  }

  return resultt{precedencet::INFIX, result};
}

ltl_sva_to_stringt::resultt
ltl_sva_to_stringt::rec(const exprt &expr, modet mode)
{
  if(mode == SVA_SEQUENCE)
    return rec_sequence(expr);
  else
    return rec_rest(expr, mode);
}

ltl_sva_to_stringt::resultt
ltl_sva_to_stringt::rec_rest(const exprt &expr, modet mode)
{
  PRECONDITION(mode == BOOLEAN || mode == PROPERTY);

  if(expr.id() == ID_and)
  {
    return infix("&", expr, mode);
  }
  else if(expr.id() == ID_or)
  {
    return infix("|", expr, mode);
  }
  else if(expr.id() == ID_xor)
  {
    return infix(" xor ", expr, mode);
  }
  else if(expr.id() == ID_implies)
  {
    return infix("->", expr, mode);
  }
  else if(expr.id() == ID_not)
  {
    return prefix("!", to_not_expr(expr), mode);
  }
  else if(expr.is_true())
  {
    // 1 is preferred, but G1 is parsed as an atom
    return resultt{precedencet::ATOM, "true"};
  }
  else if(expr.is_false())
  {
    // 0 is preferred, but G0 is parsed as an atom
    return resultt{precedencet::ATOM, "false"};
  }
  else if(expr.id() == ID_F)
  {
    return prefix("F", to_F_expr(expr), mode);
  }
  else if(expr.id() == ID_G)
  {
    return prefix("G", to_G_expr(expr), mode);
  }
  else if(expr.id() == ID_X)
  {
    return prefix("X", to_X_expr(expr), mode);
  }
  else if(expr.id() == ID_U)
  {
    return infix(" U ", expr, mode);
  }
  else if(expr.id() == ID_weak_U)
  {
    return infix(" W ", expr, mode);
  }
  else if(expr.id() == ID_R)
  {
    return infix(" R ", expr, mode);
  }
  else if(expr.id() == ID_strong_R)
  {
    return infix(" M ", expr, mode);
  }
  else if(expr.id() == ID_sva_always)
  {
    return prefix("G", to_sva_always_expr(expr), mode);
  }
  else if(expr.id() == ID_sva_ranged_always)
  {
    auto &always = to_sva_ranged_always_expr(expr);
    auto new_expr = unary_exprt{ID_sva_ranged_always, always.op()};
    auto from = numeric_cast_v<mp_integer>(always.from());
    if(!always.is_range())
      return prefix("F[" + integer2string(from) + "]", new_expr, mode);
    else if(always.is_unbounded())
      return prefix("F[" + integer2string(from) + ":]", new_expr, mode);
    else
    {
      auto to = numeric_cast_v<mp_integer>(to_constant_expr(always.to()));
      return prefix(
        "F[" + integer2string(from) + ":" + integer2string(to) + "]",
        new_expr,
        mode);
    }
  }
  else if(expr.id() == ID_sva_s_always)
  {
    auto &always = to_sva_s_always_expr(expr);
    auto new_expr = unary_exprt{ID_sva_s_always, always.op()};
    auto from = numeric_cast_v<mp_integer>(always.from());
    if(!always.is_range())
      return prefix("G[" + integer2string(from) + "]", new_expr, mode);
    else
    {
      auto to = numeric_cast_v<mp_integer>(always.to());
      return prefix(
        "G[" + integer2string(from) + ":" + integer2string(to) + "]",
        new_expr,
        mode);
    }
  }
  else if(expr.id() == ID_sva_s_eventually)
  {
    return prefix("F", to_sva_s_eventually_expr(expr), mode);
  }
  else if(
    expr.id() == ID_sva_ranged_s_eventually || expr.id() == ID_sva_eventually)
  {
    auto &eventually = to_sva_ranged_predicate_exprt(expr);
    auto new_expr = unary_exprt{expr.id(), eventually.op()};
    auto from = numeric_cast_v<mp_integer>(eventually.from());
    if(!eventually.is_range())
      return prefix("F[" + integer2string(from) + "]", new_expr, mode);
    else if(eventually.is_unbounded())
      return prefix("F[" + integer2string(from) + ":]", new_expr, mode);
    else
    {
      auto to = numeric_cast_v<mp_integer>(to_constant_expr(eventually.to()));
      return prefix(
        "F[" + integer2string(from) + ":" + integer2string(to) + "]",
        new_expr,
        mode);
    }
  }
  else if(expr.id() == ID_sva_s_nexttime)
  {
    return prefix("X", to_sva_s_nexttime_expr(expr), mode);
  }
  else if(expr.id() == ID_sva_nexttime)
  {
    return prefix("X", to_sva_nexttime_expr(expr), mode);
  }
  else if(expr.id() == ID_sva_overlapped_implication)
  {
    // maps to {f}|->g
    auto new_expr = to_sva_overlapped_implication_expr(expr);
    new_expr.sequence() = sva_sequence_property_expr_baset{
      ID_sva_implicit_weak, new_expr.sequence()};
    return infix("|->", new_expr, mode);
  }
  else if(expr.id() == ID_sva_non_overlapped_implication)
  {
    // maps to {f}|=>g
    auto new_expr = to_sva_non_overlapped_implication_expr(expr);
    new_expr.sequence() = sva_sequence_property_expr_baset{
      ID_sva_implicit_weak, new_expr.sequence()};
    return infix("|=>", new_expr, mode);
  }
  else if(expr.id() == ID_sva_overlapped_followed_by)
  {
    // 1800 2017 16.12.9
    // (a #-# b)   --->   !(a |-> !b)
    auto &followed_by = to_sva_followed_by_expr(expr);
    auto not_b = not_exprt{followed_by.consequent()};
    return rec(
      not_exprt{
        sva_overlapped_implication_exprt{followed_by.antecedent(), not_b}},
      mode);
  }
  else if(expr.id() == ID_sva_nonoverlapped_followed_by)
  {
    // 1800 2017 16.12.9
    // (a #=# b)   --->   !(a |=> !b)
    auto &followed_by = to_sva_followed_by_expr(expr);
    auto not_b = not_exprt{followed_by.consequent()};
    return rec(
      not_exprt{
        sva_non_overlapped_implication_exprt{followed_by.antecedent(), not_b}},
      mode);
  }
  else if(expr.id() == ID_sva_sequence_property)
  {
    // should have been turned into sva_implicit_weak or sva_implicit_strong
    PRECONDITION(false);
  }
  else if(expr.id() == ID_sva_s_until)
  {
    return infix(" U ", expr, mode);
  }
  else if(expr.id() == ID_sva_until)
  {
    return infix(" W ", expr, mode);
  }
  else if(expr.id() == ID_sva_s_until_with)
  {
    // This is strong release with swapped operands
    auto &until_with = to_sva_s_until_with_expr(expr);
    auto new_expr =
      strong_R_exprt{until_with.rhs(), until_with.lhs()}; // swapped
    return infix(" M ", new_expr, mode);
  }
  else if(expr.id() == ID_sva_until_with)
  {
    // This is weak release with swapped operands
    auto &until_with = to_sva_until_with_expr(expr);
    auto new_expr = R_exprt{until_with.rhs(), until_with.lhs()}; // swapped
    return infix(" R ", new_expr, mode);
  }
  else if(
    expr.id() == ID_sva_weak || expr.id() == ID_sva_strong ||
    expr.id() == ID_sva_implicit_weak || expr.id() == ID_sva_implicit_strong)
  {
    // weak closure
    auto &sequence = to_sva_sequence_property_expr_base(expr).sequence();
    auto op_rec = rec(sequence, SVA_SEQUENCE);
    return resultt{precedencet::ATOM, '{' + op_rec.s + '}'};
  }
  else if(expr.id() == ID_sva_or)
  {
    return infix("|", expr, mode);
  }
  else if(expr.id() == ID_sva_and)
  {
    return infix("&", expr, mode);
  }
  else if(expr.id() == ID_sva_boolean)
  {
    return rec(to_sva_boolean_expr(expr).op(), BOOLEAN);
  }
  else if(expr.id() == ID_if)
  {
    // c ? x : y  --->  (c∧x)∨(¬c∧y)
    auto &if_expr = to_if_expr(expr);
    auto a1 = and_exprt{if_expr.cond(), if_expr.true_case()};
    auto a2 = and_exprt{not_exprt{if_expr.cond()}, if_expr.false_case()};
    return rec(or_exprt{a1, a2}, mode);
  }
  else if(!is_temporal_operator(expr))
  {
    auto number = atoms.number(expr);

    // a0, a1, a2, a3, a4, ...
    std::string s = "a" + std::to_string(number);

    return resultt{precedencet::ATOM, s};
  }
  else
    throw ebmc_errort{} << "cannot convert property " << expr.id()
                        << " to Buechi";
}

ltl_sva_to_stringt::resultt ltl_sva_to_stringt::rec_sequence(const exprt &expr)
{
  if(expr.id() == ID_sva_or)
  {
    return infix("|", expr, SVA_SEQUENCE);
  }
  else if(expr.id() == ID_sva_and)
  {
    // NLM intersection
    return infix("&", expr, SVA_SEQUENCE);
  }
  else if(expr.id() == ID_sva_sequence_intersect)
  {
    return infix("&&", expr, SVA_SEQUENCE);
  }
  else if(expr.id() == ID_sva_boolean)
  {
    return rec(to_sva_boolean_expr(expr).op(), BOOLEAN);
  }
  else if(expr.id() == ID_sva_cycle_delay)
  {
    auto &delay = to_sva_cycle_delay_expr(expr);

    if(delay.lhs().is_nil())
    {
      auto new_expr = unary_exprt{expr.id(), delay.rhs()};

      if(delay.is_range()) // ##[from:to] rhs
      {
        auto from = numeric_cast_v<mp_integer>(delay.from());

        if(delay.is_unbounded()) // ##[n:$] rhs
        {
          return prefix(
            "1[*" + integer2string(from) + "..] ; ", new_expr, SVA_SEQUENCE);
        }
        else
        {
          auto to = numeric_cast_v<mp_integer>(delay.to());
          PRECONDITION(to >= 0);
          return prefix(
            "1[*" + integer2string(from) + ".." + integer2string(to) + "] ; ",
            new_expr,
            SVA_SEQUENCE);
        }
      }
      else // ##n rhs
      {
        auto i = numeric_cast_v<mp_integer>(delay.from());
        PRECONDITION(i >= 0);
        return prefix(
          "1[*" + integer2string(i) + "] ; ", new_expr, SVA_SEQUENCE);
      }
    }
    else // lhs is not nil
    {
      // We special-case the following for better readability:
      // f ##0 g  --> f : g
      // f ##1 g  --> f ; g
      // f ##n g  --> f ; 1[*n-1] ; b
      auto new_expr =
        binary_exprt{delay.lhs(), delay.id(), delay.rhs(), delay.type()};

      if(delay.is_range())
      {
        auto from = numeric_cast_v<mp_integer>(delay.from());

        if(from == 0)
        {
          // requires treatment of empty sequences on lhs
          throw ebmc_errort{}
            << "cannot convert 0.. ranged sequence concatenation to Buechi";
        }
        else if(delay.is_unbounded()) // f ##[n:$] g
        {
          return infix(
            " ; 1[*" + integer2string(from - 1) + "..] ; ",
            new_expr,
            SVA_SEQUENCE);
        }
        else // f ##[from:to] g
        {
          auto to = numeric_cast_v<mp_integer>(delay.to());
          PRECONDITION(to >= 0);
          return infix(
            " ; 1[*" + integer2string(from - 1) + ".." +
              integer2string(to - 1) + "] ; ",
            new_expr,
            SVA_SEQUENCE);
        }
      }
      else // f ##n g
      {
        auto n = numeric_cast_v<mp_integer>(delay.from());
        PRECONDITION(n >= 0);
        if(n == 0)
          return infix(" : ", new_expr, SVA_SEQUENCE);
        else if(n == 1)
          return infix(" ; ", new_expr, SVA_SEQUENCE);
        else
        {
          return infix(
            " ; 1[*" + integer2string(n - 1) + "] ; ", new_expr, SVA_SEQUENCE);
        }
      }
    }
  }
  else if(expr.id() == ID_sva_cycle_delay_star) // ##[*] something
  {
    auto new_expr = unary_exprt{
      ID_sva_cycle_delay_star, to_sva_cycle_delay_star_expr(expr).rhs()};
    return suffix("[*]", new_expr, SVA_SEQUENCE);
  }
  else if(expr.id() == ID_sva_cycle_delay_plus) // ##[+] something
  {
    auto new_expr = unary_exprt{
      ID_sva_cycle_delay_star, to_sva_cycle_delay_plus_expr(expr).rhs()};
    return suffix("[+]", new_expr, SVA_SEQUENCE);
  }
  else if(
    expr.id() ==
    ID_sva_sequence_repetition_star) // [*] or [*n] or [*x:y] or [*x:$]
  {
    auto &repetition = to_sva_sequence_repetition_star_expr(expr);
    unary_exprt new_expr{ID_sva_sequence_repetition_star, repetition.op()};
    if(!repetition.repetitions_given())
    {
      return suffix("[*]", new_expr, SVA_SEQUENCE);
    }
    else if(repetition.is_empty_match())
    {
      throw ebmc_errort{} << "cannot convert [*0] to Buechi";
    }
    else if(repetition.is_singleton())
    {
      auto n = numeric_cast_v<mp_integer>(repetition.repetitions());
      return suffix("[*" + integer2string(n) + "]", new_expr, SVA_SEQUENCE);
    }
    else if(repetition.is_bounded_range())
    {
      auto from = numeric_cast_v<mp_integer>(repetition.from());
      auto to = numeric_cast_v<mp_integer>(repetition.to());
      return suffix(
        "[*" + integer2string(from) + ".." + integer2string(to) + "]",
        new_expr,
        SVA_SEQUENCE);
    }
    else if(repetition.is_unbounded())
    {
      auto from = numeric_cast_v<mp_integer>(repetition.from());
      return suffix(
        "[*" + integer2string(from) + "..]", new_expr, SVA_SEQUENCE);
    }
    else
      DATA_INVARIANT(false, "unexpected sva_sequence_repetition_star");
  }
  else if(expr.id() == ID_sva_sequence_repetition_plus) // something[+]
  {
    auto new_expr = unary_exprt{
      ID_sva_sequence_repetition_plus,
      to_sva_sequence_repetition_plus_expr(expr).op()};
    return suffix("[+]", new_expr, SVA_SEQUENCE);
  }
  else if(expr.id() == ID_sva_sequence_goto_repetition) // something[->n]
  {
    auto &repetition = to_sva_sequence_goto_repetition_expr(expr);
    unary_exprt new_expr{ID_sva_sequence_goto_repetition, repetition.op()};
    if(repetition.is_singleton())
    {
      auto n = numeric_cast_v<mp_integer>(repetition.repetitions());
      return suffix("[->" + integer2string(n) + "]", new_expr, SVA_SEQUENCE);
    }
    else if(repetition.is_bounded_range())
    {
      auto from = numeric_cast_v<mp_integer>(repetition.from());
      auto to = numeric_cast_v<mp_integer>(repetition.to());
      return suffix(
        "[->" + integer2string(from) + ".." + integer2string(to) + "]",
        new_expr,
        SVA_SEQUENCE);
    }
    else if(repetition.is_unbounded())
    {
      auto from = numeric_cast_v<mp_integer>(repetition.from());
      return suffix(
        "[->" + integer2string(from) + "..]", new_expr, SVA_SEQUENCE);
    }
    else
      DATA_INVARIANT(false, "unexpected sva_sequence_goto_repetition");
  }
  else if(
    expr.id() == ID_sva_sequence_non_consecutive_repetition) // something[=n]
  {
    auto &repetition = to_sva_sequence_non_consecutive_repetition_expr(expr);
    unary_exprt new_expr{
      ID_sva_sequence_non_consecutive_repetition, repetition.op()};
    if(repetition.is_singleton())
    {
      auto n = numeric_cast_v<mp_integer>(repetition.repetitions());
      return suffix("[=" + integer2string(n) + "]", new_expr, SVA_SEQUENCE);
    }
    else if(repetition.is_bounded_range())
    {
      auto from = numeric_cast_v<mp_integer>(repetition.from());
      auto to = numeric_cast_v<mp_integer>(repetition.to());
      return suffix(
        "[=" + integer2string(from) + ".." + integer2string(to) + "]",
        new_expr,
        SVA_SEQUENCE);
    }
    else if(repetition.is_unbounded())
    {
      auto from = numeric_cast_v<mp_integer>(repetition.from());
      return suffix(
        "[=" + integer2string(from) + "..]", new_expr, SVA_SEQUENCE);
    }
    else
      DATA_INVARIANT(
        false, "unexpected sva_sequence_non_consecutive_repetition");
  }
  else
    throw ebmc_errort{} << "cannot convert sequence " << expr.id()
                        << " to Buechi";
}
