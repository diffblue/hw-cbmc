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
ltl_sva_to_stringt::suffix(std::string s, const exprt &expr, modet mode)
{
  auto op_rec = rec(to_unary_expr(expr).op(), mode);

  auto new_e = to_unary_expr(expr);
  new_e.op() = op_rec.e;

  if(op_rec.p == precedencet::ATOM || op_rec.p == precedencet::SUFFIX)
    return resultt{precedencet::SUFFIX, op_rec.s + s, new_e};
  else
    return resultt{precedencet::SUFFIX, '(' + op_rec.s + ')' + s, new_e};
}

ltl_sva_to_stringt::resultt
ltl_sva_to_stringt::prefix(std::string s, const exprt &expr, modet mode)
{
  auto op_rec = rec(to_unary_expr(expr).op(), mode);

  auto new_e = to_unary_expr(expr);
  new_e.op() = op_rec.e;

  if(op_rec.p == precedencet::ATOM || op_rec.p == precedencet::PREFIX)
    return resultt{precedencet::PREFIX, s + op_rec.s, new_e};
  else
    return resultt{precedencet::PREFIX, s + '(' + op_rec.s + ')', new_e};
}

ltl_sva_to_stringt::resultt
ltl_sva_to_stringt::infix(std::string s, const exprt &expr, modet mode)
{
  std::string result;
  bool first = true;
  exprt new_e = expr; // copy

  for(auto &op : new_e.operands())
  {
    if(first)
      first = false;
    else
      result += s;

    auto op_rec = rec(op, mode);
    op = op_rec.e;

    if(op_rec.p == precedencet::ATOM)
      result += op_rec.s;
    else
      result += '(' + op_rec.s + ')';
  }

  return resultt{precedencet::INFIX, result, new_e};
}

ltl_sva_to_stringt::resultt
ltl_sva_to_stringt::rec(const exprt &expr, modet mode)
{
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
    return prefix("!", expr, mode);
  }
  else if(expr.is_true())
  {
    // 1 is preferred, but G1 is parsed as an atom
    return resultt{precedencet::ATOM, "true", expr};
  }
  else if(expr.is_false())
  {
    // 0 is preferred, but G0 is parsed as an atom
    return resultt{precedencet::ATOM, "false", expr};
  }
  else if(expr.id() == ID_F)
  {
    PRECONDITION(mode == PROPERTY);
    return prefix("F", expr, mode);
  }
  else if(expr.id() == ID_G)
  {
    PRECONDITION(mode == PROPERTY);
    return prefix("G", expr, mode);
  }
  else if(expr.id() == ID_X)
  {
    PRECONDITION(mode == PROPERTY);
    return prefix("X", expr, mode);
  }
  else if(expr.id() == ID_U)
  {
    PRECONDITION(mode == PROPERTY);
    return infix(" U ", expr, mode);
  }
  else if(expr.id() == ID_weak_U)
  {
    PRECONDITION(mode == PROPERTY);
    return infix(" W ", expr, mode);
  }
  else if(expr.id() == ID_R)
  {
    PRECONDITION(mode == PROPERTY);
    return infix(" R ", expr, mode);
  }
  else if(expr.id() == ID_strong_R)
  {
    PRECONDITION(mode == PROPERTY);
    return infix(" M ", expr, mode);
  }
  else if(expr.id() == ID_sva_always)
  {
    PRECONDITION(mode == PROPERTY);
    return prefix("G", expr, mode);
  }
  else if(expr.id() == ID_sva_ranged_always)
  {
    auto &always = to_sva_ranged_always_expr(expr);
    auto new_expr = unary_exprt{ID_sva_ranged_always, always.op()};
    auto lower = numeric_cast_v<mp_integer>(always.lower());
    if(!always.is_range())
      return prefix("F[" + integer2string(lower) + "]", new_expr, mode);
    else if(always.is_unbounded())
      return prefix("F[" + integer2string(lower) + ":]", new_expr, mode);
    else
    {
      auto upper = numeric_cast_v<mp_integer>(to_constant_expr(always.upper()));
      return prefix(
        "F[" + integer2string(lower) + ":" + integer2string(upper) + "]",
        new_expr,
        mode);
    }
  }
  else if(expr.id() == ID_sva_s_always)
  {
    throw ebmc_errort{} << "cannot convert " << expr.id() << " to Buechi";
  }
  else if(expr.id() == ID_sva_s_eventually)
  {
    PRECONDITION(mode == PROPERTY);
    return prefix("F", expr, mode);
  }
  else if(
    expr.id() == ID_sva_ranged_s_eventually || expr.id() == ID_sva_eventually)
  {
    PRECONDITION(mode == PROPERTY);
    auto &eventually = to_sva_ranged_predicate_exprt(expr);
    auto new_expr = unary_exprt{expr.id(), eventually.op()};
    auto lower = numeric_cast_v<mp_integer>(eventually.lower());
    if(!eventually.is_range())
      return prefix("F[" + integer2string(lower) + "]", new_expr, mode);
    else if(eventually.is_unbounded())
      return prefix("F[" + integer2string(lower) + ":]", new_expr, mode);
    else
    {
      auto upper =
        numeric_cast_v<mp_integer>(to_constant_expr(eventually.upper()));
      return prefix(
        "F[" + integer2string(lower) + ":" + integer2string(upper) + "]",
        new_expr,
        mode);
    }
  }
  else if(expr.id() == ID_sva_s_nexttime)
  {
    PRECONDITION(mode == PROPERTY);
    return prefix("X", expr, mode);
  }
  else if(expr.id() == ID_sva_nexttime)
  {
    PRECONDITION(mode == PROPERTY);
    return prefix("X", expr, mode);
  }
  else if(expr.id() == ID_sva_overlapped_implication)
  {
    // maps to {f}|->g
    PRECONDITION(mode == PROPERTY);
    auto new_expr = to_sva_overlapped_implication_expr(expr);
    new_expr.sequence() = sva_sequence_property_expr_baset{
      ID_sva_implicit_weak, new_expr.sequence()};
    return infix("|->", new_expr, mode);
  }
  else if(expr.id() == ID_sva_non_overlapped_implication)
  {
    // maps to {f}|=>g
    PRECONDITION(mode == PROPERTY);
    auto new_expr = to_sva_non_overlapped_implication_expr(expr);
    new_expr.sequence() = sva_sequence_property_expr_baset{
      ID_sva_implicit_weak, new_expr.sequence()};
    return infix("|=>", new_expr, mode);
  }
  else if(
    expr.id() == ID_sva_nonoverlapped_followed_by ||
    expr.id() == ID_sva_overlapped_followed_by)
  {
    PRECONDITION(mode == PROPERTY);
    throw ebmc_errort{} << "cannot convert " << expr.id() << " to Buechi";
  }
  else if(expr.id() == ID_sva_sequence_property)
  {
    // should have been turned into sva_implicit_weak or sva_implicit_strong
    PRECONDITION(false);
  }
  else if(expr.id() == ID_sva_s_until)
  {
    PRECONDITION(mode == PROPERTY);
    return infix(" U ", expr, mode);
  }
  else if(expr.id() == ID_sva_s_until_with)
  {
    // This is release with swapped operands
    PRECONDITION(mode == PROPERTY);
    auto &until_with = to_sva_s_until_with_expr(expr);
    auto R = R_exprt{until_with.rhs(), until_with.lhs()}; // swapped
    return rec(R, mode);
  }
  else if(
    expr.id() == ID_sva_weak || expr.id() == ID_sva_strong ||
    expr.id() == ID_sva_implicit_weak || expr.id() == ID_sva_implicit_strong)
  {
    PRECONDITION(mode == PROPERTY);
    // weak closure
    auto &sequence = to_sva_sequence_property_expr_base(expr).sequence();
    auto op_rec = rec(sequence, SVA_SEQUENCE);
    return resultt{precedencet::ATOM, '{' + op_rec.s + '}', expr};
  }
  else if(expr.id() == ID_sva_or)
  {
    // can be sequence or property
    PRECONDITION(mode == PROPERTY || mode == SVA_SEQUENCE);
    return infix("|", expr, mode);
  }
  else if(expr.id() == ID_sva_and)
  {
    // can be sequence or property
    PRECONDITION(mode == PROPERTY || mode == SVA_SEQUENCE);
    // NLM intersection
    return infix("&", expr, mode);
  }
  else if(expr.id() == ID_sva_sequence_intersect)
  {
    PRECONDITION(mode == SVA_SEQUENCE);
    return infix("&&", expr, mode);
  }
  else if(expr.id() == ID_sva_boolean)
  {
    // can be sequence or property
    PRECONDITION(mode == PROPERTY || mode == SVA_SEQUENCE);
    return rec(to_sva_boolean_expr(expr).op(), BOOLEAN);
  }
  else if(expr.id() == ID_sva_sequence_concatenation)
  {
    PRECONDITION(mode == SVA_SEQUENCE);
    // SVA sequence concatenation is overlapping, whereas
    // the ; operator is nonoverlapping. We special-case
    // the following for better readability:
    // f ##0 g  --> f : g
    // f ##1 g  --> f ; g
    // f ##n g  --> f ; 1[*n-1] ; b
    auto &concatenation = to_sva_sequence_concatenation_expr(expr);
    if(concatenation.rhs().id() == ID_sva_cycle_delay)
    {
      auto &delay = to_sva_cycle_delay_expr(concatenation.rhs());

      auto new_expr = concatenation;
      new_expr.rhs() = delay.op();

      if(delay.is_range())
      {
        auto from = numeric_cast_v<mp_integer>(delay.from());

        if(from == 0)
        {
          // requires treatment of empty sequences on lhs
          throw ebmc_errort{}
            << "cannot convert 0.. ranged sequence concatenation to Buechi";
        }
        else if(delay.is_unbounded())
        {
          return infix(
            " ; 1[*" + integer2string(from - 1) + "..] ; ", new_expr, mode);
        }
        else
        {
          auto to = numeric_cast_v<mp_integer>(delay.to());
          PRECONDITION(to >= 0);
          return infix(
            " ; 1[*" + integer2string(from - 1) + ".." +
              integer2string(to - 1) + "] ; ",
            new_expr,
            mode);
        }
      }
      else
      {
        auto n = numeric_cast_v<mp_integer>(delay.from());
        PRECONDITION(n >= 0);
        if(n == 0)
          return infix(" : ", new_expr, mode);
        else if(n == 1)
          return infix(" ; ", new_expr, mode);
        else
        {
          return infix(
            " ; 1[*" + integer2string(n - 1) + "] ; ", new_expr, mode);
        }
      }
    }
    else
      return infix(":", expr, mode);
  }
  else if(expr.id() == ID_sva_cycle_delay)
  {
    PRECONDITION(mode == SVA_SEQUENCE);
    auto &delay = to_sva_cycle_delay_expr(expr);
    unary_exprt new_expr{expr.id(), delay.op()};

    if(delay.is_range())
    {
      auto from = numeric_cast_v<mp_integer>(delay.from());

      if(delay.is_unbounded())
      {
        return prefix("1[*" + integer2string(from) + "..] ; ", new_expr, mode);
      }
      else
      {
        auto to = numeric_cast_v<mp_integer>(delay.to());
        PRECONDITION(to >= 0);
        return prefix(
          "1[*" + integer2string(from) + ".." + integer2string(to) + "] ; ",
          new_expr,
          mode);
      }
    }
    else // singleton
    {
      auto i = numeric_cast_v<mp_integer>(delay.from());
      PRECONDITION(i >= 0);
      return prefix("1[*" + integer2string(i) + "] ; ", new_expr, mode);
    }
  }
  else if(expr.id() == ID_sva_cycle_delay_star) // ##[*] something
  {
    PRECONDITION(mode == SVA_SEQUENCE);
    return suffix("[*]", expr, mode);
  }
  else if(expr.id() == ID_sva_cycle_delay_plus) // ##[+] something
  {
    PRECONDITION(mode == SVA_SEQUENCE);
    return suffix("[+]", expr, mode);
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

    symbol_exprt new_e{s, expr.type()};

    return resultt{precedencet::ATOM, s, new_e};
  }
  else
    throw ebmc_errort{} << "cannot convert " << expr.id() << " to Buechi";
}
