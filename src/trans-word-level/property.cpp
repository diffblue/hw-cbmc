/*******************************************************************\

Module: Unwinding the Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "property.h"

#include <util/arith_tools.h>
#include <util/ebmc_util.h>
#include <util/expr_iterator.h>
#include <util/expr_util.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <ebmc/ebmc_error.h>
#include <temporal-logic/temporal_expr.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

#include "instantiate_word_level.h"
#include "obligations.h"

#include <cstdlib>

/*******************************************************************\

Function: bmc_supports_LTL_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmc_supports_LTL_property(const exprt &expr)
{
  return true;
}

/*******************************************************************\

Function: bmc_supports_CTL_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmc_supports_CTL_property(const exprt &expr)
{
  // We map a subset of ACTL to LTL, following
  // Monika Maidl. "The common fragment of CTL and LTL"
  // http://dx.doi.org/10.1109/SFCS.2000.892332
  //
  // Specificially, we allow
  // * state predicates
  // * conjunctions of allowed formulas
  // * AX φ, where φ is allowed
  // * AF φ, where φ is allowed
  // * AG φ, where φ is allowed
  if(!has_CTL_operator(expr))
  {
    return true;
  }
  else if(expr.id() == ID_and)
  {
    for(auto &op : expr.operands())
      if(!bmc_supports_CTL_property(op))
        return false;
    return true;
  }
  else if(expr.id() == ID_AX)
  {
    return bmc_supports_CTL_property(to_AX_expr(expr).op());
  }
  else if(expr.id() == ID_AF)
  {
    return bmc_supports_CTL_property(to_AF_expr(expr).op());
  }
  else if(expr.id() == ID_AG)
  {
    return bmc_supports_CTL_property(to_AG_expr(expr).op());
  }
  else
    return false;
}

/*******************************************************************\

Function: bmc_supports_SVA_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmc_supports_SVA_property(const exprt &expr)
{
  // sva_nonoverlapped_followed_by is not supported yet
  if(has_subexpr(expr, ID_sva_nonoverlapped_followed_by))
    return false;

  // sva_overlapped_followed_by is not supported yet
  if(has_subexpr(expr, ID_sva_overlapped_followed_by))
    return false;

  return true;
}

/*******************************************************************\

Function: bmc_supports_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmc_supports_property(const exprt &expr)
{
  if(is_LTL(expr))
    return bmc_supports_LTL_property(expr);
  else if(is_CTL(expr))
    return bmc_supports_CTL_property(expr);
  else if(is_SVA(expr))
    return bmc_supports_SVA_property(expr);
  else
    return false; // unknown category
}

/*******************************************************************\

Function: property_obligations_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static obligationst property_obligations_rec(
  const exprt &property_expr,
  decision_proceduret &solver,
  const mp_integer &current,
  const mp_integer &no_timeframes,
  const namespacet &ns)
{
  PRECONDITION(current >= 0 && current < no_timeframes);

  if(
    property_expr.id() == ID_AG || property_expr.id() == ID_G ||
    property_expr.id() == ID_sva_always)
  {
    // We want AG phi.
    auto &phi = [](const exprt &expr) -> const exprt & {
      if(expr.id() == ID_AG)
        return to_AG_expr(expr).op();
      else if(expr.id() == ID_G)
        return to_G_expr(expr).op();
      else if(expr.id() == ID_sva_always)
        return to_sva_always_expr(expr).op();
      else
        PRECONDITION(false);
    }(property_expr);

    obligationst obligations;

    for(mp_integer c = current; c < no_timeframes; ++c)
    {
      obligations.add(
        property_obligations_rec(phi, solver, c, no_timeframes, ns));
    }

    return obligations;
  }
  else if(property_expr.id() == ID_sva_eventually)
  {
    const auto &eventually_expr = to_sva_eventually_expr(property_expr);
    const auto &op = eventually_expr.op();

    mp_integer lower;
    if(to_integer_non_constant(eventually_expr.lower(), lower))
      throw "failed to convert sva_eventually index";

    mp_integer upper;
    if(to_integer_non_constant(eventually_expr.upper(), upper))
      throw "failed to convert sva_eventually index";

    // We rely on NNF.
    if(current + lower >= no_timeframes || current + upper >= no_timeframes)
    {
      DATA_INVARIANT(no_timeframes != 0, "must have timeframe");
      return obligationst{no_timeframes - 1, true_exprt()};
    }

    exprt::operandst disjuncts = {};

    for(mp_integer u = current + lower; u <= current + upper; ++u)
    {
      auto obligations_rec =
        property_obligations_rec(op, solver, u, no_timeframes, ns);
      disjuncts.push_back(obligations_rec.conjunction().second);
    }

    DATA_INVARIANT(no_timeframes != 0, "must have timeframe");
    return obligationst{no_timeframes - 1, disjunction(disjuncts)};
  }
  else if(
    property_expr.id() == ID_AF || property_expr.id() == ID_F ||
    property_expr.id() == ID_sva_s_eventually)
  {
    const auto &phi = to_unary_expr(property_expr).op();

    obligationst obligations;

    // Counterexamples to Fφ must have a loop.
    // We consider l-k loops with l<k.
    for(mp_integer k = current + 1; k < no_timeframes; ++k)
    {
      // The following needs to be satisfied for a counterexample
      // to Fφ that loops back in timeframe k:
      //
      // (1) There is a loop from timeframe k back to
      //     some earlier state l with current<=l<k.
      // (2) No state j with current<=j<=k to the end of the
      //     lasso satisfies 'φ'.
      for(mp_integer l = current; l < k; ++l)
      {
        exprt::operandst disjuncts = {not_exprt(lasso_symbol(l, k))};

        for(mp_integer j = current; j <= k; ++j)
        {
          auto tmp =
            property_obligations_rec(phi, solver, j, no_timeframes, ns);
          disjuncts.push_back(tmp.conjunction().second);
        }

        obligations.add(k, disjunction(disjuncts));
      }
    }

    return obligations;
  }
  else if(property_expr.id() == ID_sva_ranged_s_eventually)
  {
    auto &phi = to_sva_ranged_s_eventually_expr(property_expr).op();
    auto &lower = to_sva_ranged_s_eventually_expr(property_expr).lower();
    auto &upper = to_sva_ranged_s_eventually_expr(property_expr).upper();

    auto from_opt = numeric_cast<mp_integer>(lower);
    if(!from_opt.has_value())
      throw ebmc_errort() << "failed to convert SVA s_eventually from index";

    if(*from_opt < 0)
      throw ebmc_errort() << "SVA s_eventually from index must not be negative";

    auto from = std::min(no_timeframes - 1, current + *from_opt);

    mp_integer to;

    if(upper.id() == ID_infinity)
    {
      throw ebmc_errort()
        << "failed to convert SVA s_eventually to index (infinity)";
    }
    else
    {
      auto to_opt = numeric_cast<mp_integer>(upper);
      if(!to_opt.has_value())
        throw ebmc_errort() << "failed to convert SVA s_eventually to index";
      to = std::min(current + *to_opt, no_timeframes - 1);
    }

    exprt::operandst disjuncts;
    mp_integer time = 0;

    for(mp_integer c = from; c <= to; ++c)
    {
      auto tmp = property_obligations_rec(phi, solver, c, no_timeframes, ns)
                   .conjunction();
      time = std::max(time, tmp.first);
      disjuncts.push_back(tmp.second);
    }

    return obligationst{time, disjunction(disjuncts)};
  }
  else if(
    property_expr.id() == ID_sva_ranged_always ||
    property_expr.id() == ID_sva_s_always)
  {
    auto &phi = property_expr.id() == ID_sva_ranged_always
                  ? to_sva_ranged_always_expr(property_expr).op()
                  : to_sva_s_always_expr(property_expr).op();
    auto &lower = property_expr.id() == ID_sva_ranged_always
                    ? to_sva_ranged_always_expr(property_expr).lower()
                    : to_sva_s_always_expr(property_expr).lower();
    auto &upper = property_expr.id() == ID_sva_ranged_always
                    ? to_sva_ranged_always_expr(property_expr).upper()
                    : to_sva_s_always_expr(property_expr).upper();

    auto from_opt = numeric_cast<mp_integer>(lower);
    if(!from_opt.has_value())
      throw ebmc_errort() << "failed to convert SVA always from index";

    if(*from_opt < 0)
      throw ebmc_errort() << "SVA always from index must not be negative";

    auto from = current + *from_opt;

    mp_integer to;

    if(upper.id() == ID_infinity)
    {
      to = no_timeframes - 1;
    }
    else
    {
      auto to_opt = numeric_cast<mp_integer>(upper);
      if(!to_opt.has_value())
        throw ebmc_errort() << "failed to convert SVA always to index";
      to = std::min(current + *to_opt, no_timeframes - 1);
    }

    obligationst obligations;

    for(mp_integer c = from; c <= to; ++c)
    {
      obligations.add(
        property_obligations_rec(phi, solver, c, no_timeframes, ns));
    }

    return obligations;
  }
  else if(
    property_expr.id() == ID_X || property_expr.id() == ID_sva_nexttime ||
    property_expr.id() == ID_sva_s_nexttime)
  {
    const auto next = current + 1;

    auto &phi = [](const exprt &expr) -> const exprt &
    {
      if(expr.id() == ID_X)
        return to_X_expr(expr).op();
      else if(expr.id() == ID_sva_nexttime)
        return to_sva_nexttime_expr(expr).op();
      else if(expr.id() == ID_sva_s_nexttime)
        return to_sva_s_nexttime_expr(expr).op();
      else
        PRECONDITION(false);
    }(property_expr);

    if(next < no_timeframes)
    {
      return property_obligations_rec(phi, solver, next, no_timeframes, ns);
    }
    else
    {
      DATA_INVARIANT(no_timeframes != 0, "must have timeframe");
      return obligationst{no_timeframes - 1, true_exprt()}; // works on NNF only
    }
  }
  else if(property_expr.id() == ID_sva_s_until || property_expr.id() == ID_U)
  {
    auto &p = to_binary_expr(property_expr).lhs();
    auto &q = to_binary_expr(property_expr).rhs();

    // p U q ≡ Fq ∧ (p W q)
    exprt tmp = and_exprt{F_exprt{q}, weak_U_exprt{p, q}};

    return property_obligations_rec(tmp, solver, current, no_timeframes, ns);
  }
  else if(property_expr.id() == ID_sva_until || property_expr.id() == ID_weak_U)
  {
    // we expand: p W q ≡ q ∨ ( p ∧ X(p W q) )
    auto &p = to_binary_expr(property_expr).lhs();
    auto &q = to_binary_expr(property_expr).rhs();

    // Once we reach the end of the unwinding, replace X(p W q) by 'true'.
    auto tmp = or_exprt{
      q,
      (current + 1) < no_timeframes ? and_exprt{p, X_exprt{property_expr}} : p};

    return property_obligations_rec(tmp, solver, current, no_timeframes, ns);
  }
  else if(property_expr.id() == ID_R)
  {
    // we expand: p R q <=> q ∧ (p ∨ X(p R q))
    auto &R_expr = to_R_expr(property_expr);
    auto &p = R_expr.lhs();
    auto &q = R_expr.rhs();

    // Once we reach the end of the unwinding, we replace X(p R q) by
    // true, and hence the expansion becomes "q" only.
    exprt expansion = (current + 1) < no_timeframes
                        ? and_exprt{q, or_exprt{p, X_exprt{property_expr}}}
                        : q;

    return property_obligations_rec(
      expansion, solver, current, no_timeframes, ns);
  }
  else if(property_expr.id() == ID_strong_R)
  {
    auto &p = to_strong_R_expr(property_expr).lhs();
    auto &q = to_strong_R_expr(property_expr).rhs();

    // p strongR q ≡ Fp ∧ (p R q)
    exprt tmp = and_exprt{F_exprt{q}, weak_U_exprt{p, q}};

    return property_obligations_rec(tmp, solver, current, no_timeframes, ns);
  }
  else if(property_expr.id() == ID_sva_until_with)
  {
    // Rewrite to LTL (weak) R.
    // Note that lhs and rhs are flipped.
    auto &until_with = to_sva_until_with_expr(property_expr);
    auto R = R_exprt{until_with.rhs(), until_with.lhs()};
    return property_obligations_rec(R, solver, current, no_timeframes, ns);
  }
  else if(property_expr.id() == ID_sva_s_until_with)
  {
    // Rewrite to LTL (strong) R.
    // Note that lhs and rhs are flipped.
    auto &s_until_with = to_sva_s_until_with_expr(property_expr);
    auto strong_R = strong_R_exprt{s_until_with.rhs(), s_until_with.lhs()};
    return property_obligations_rec(
      strong_R, solver, current, no_timeframes, ns);
  }
  else if(property_expr.id() == ID_and)
  {
    // Generate seperate sets of obligations for each conjunct,
    // and then return the union.
    obligationst obligations;

    for(auto &op : to_and_expr(property_expr).operands())
    {
      obligations.add(
        property_obligations_rec(op, solver, current, no_timeframes, ns));
    }

    return obligations;
  }
  else if(property_expr.id() == ID_or)
  {
    // Generate seperate obligations for each disjunct,
    // and then 'or' these.
    mp_integer t = 0;
    exprt::operandst disjuncts;
    obligationst obligations;

    for(auto &op : to_or_expr(property_expr).operands())
    {
      auto obligations =
        property_obligations_rec(op, solver, current, no_timeframes, ns);
      auto conjunction = obligations.conjunction();
      t = std::max(t, conjunction.first);
      disjuncts.push_back(conjunction.second);
    }

    return obligationst{t, disjunction(disjuncts)};
  }
  else if(
    property_expr.id() == ID_equal &&
    to_equal_expr(property_expr).lhs().type().id() == ID_bool)
  {
    // we rely on NNF: a<=>b ---> a=>b && b=>a
    auto &equal_expr = to_equal_expr(property_expr);
    auto tmp = and_exprt{
      implies_exprt{equal_expr.lhs(), equal_expr.rhs()},
      implies_exprt{equal_expr.rhs(), equal_expr.lhs()}};
    return property_obligations_rec(tmp, solver, current, no_timeframes, ns);
  }
  else if(property_expr.id() == ID_implies)
  {
    // we rely on NNF
    auto &implies_expr = to_implies_expr(property_expr);
    auto tmp = or_exprt{not_exprt{implies_expr.lhs()}, implies_expr.rhs()};
    return property_obligations_rec(tmp, solver, current, no_timeframes, ns);
  }
  else if(property_expr.id() == ID_if)
  {
    // we rely on NNF
    auto &if_expr = to_if_expr(property_expr);
    auto cond =
      instantiate_property(if_expr.cond(), current, no_timeframes, ns).second;
    auto obligations_true =
      property_obligations_rec(
        if_expr.true_case(), solver, current, no_timeframes, ns)
        .conjunction();
    auto obligations_false =
      property_obligations_rec(
        if_expr.false_case(), solver, current, no_timeframes, ns)
        .conjunction();
    return obligationst{
      std::max(obligations_true.first, obligations_false.first),
      if_exprt{cond, obligations_true.second, obligations_false.second}};
  }
  else if(
    property_expr.id() == ID_typecast &&
    to_typecast_expr(property_expr).op().type().id() == ID_bool)
  {
    // drop reduntant type casts
    return property_obligations_rec(
      to_typecast_expr(property_expr).op(), solver, current, no_timeframes, ns);
  }
  else if(property_expr.id() == ID_not)
  {
    // We need NNF, try to eliminate the negation.
    auto &op = to_not_expr(property_expr).op();

    if(op.id() == ID_U)
    {
      // ¬(φ U ψ) ≡ (¬φ R ¬ψ)
      auto &U = to_U_expr(op);
      auto R = R_exprt{not_exprt{U.lhs()}, not_exprt{U.rhs()}};
      return property_obligations_rec(R, solver, current, no_timeframes, ns);
    }
    else if(op.id() == ID_R)
    {
      // ¬(φ R ψ) ≡ (¬φ U ¬ψ)
      auto &R = to_R_expr(op);
      auto U = U_exprt{not_exprt{R.lhs()}, not_exprt{R.rhs()}};
      return property_obligations_rec(U, solver, current, no_timeframes, ns);
    }
    else if(op.id() == ID_G)
    {
      // ¬G φ ≡ F ¬φ
      auto &G = to_G_expr(op);
      auto F = F_exprt{not_exprt{G.op()}};
      return property_obligations_rec(F, solver, current, no_timeframes, ns);
    }
    else if(op.id() == ID_F)
    {
      // ¬F φ ≡ G ¬φ
      auto &F = to_F_expr(op);
      auto G = G_exprt{not_exprt{F.op()}};
      return property_obligations_rec(G, solver, current, no_timeframes, ns);
    }
    else if(op.id() == ID_X)
    {
      // ¬X φ ≡ X ¬φ
      auto &X = to_X_expr(op);
      auto negX = X_exprt{not_exprt{X.op()}};
      return property_obligations_rec(negX, solver, current, no_timeframes, ns);
    }
    else if(op.id() == ID_implies)
    {
      // ¬(a->b) --> a && ¬b
      auto &implies_expr = to_implies_expr(op);
      auto and_expr =
        and_exprt{implies_expr.lhs(), not_exprt{implies_expr.rhs()}};
      return property_obligations_rec(
        and_expr, solver, current, no_timeframes, ns);
    }
    else if(op.id() == ID_and)
    {
      auto operands = op.operands();
      for(auto &op : operands)
        op = not_exprt{op};
      auto or_expr = or_exprt{std::move(operands)};
      return property_obligations_rec(
        or_expr, solver, current, no_timeframes, ns);
    }
    else if(op.id() == ID_or)
    {
      auto operands = op.operands();
      for(auto &op : operands)
        op = not_exprt{op};
      auto and_expr = and_exprt{std::move(operands)};
      return property_obligations_rec(
        and_expr, solver, current, no_timeframes, ns);
    }
    else if(op.id() == ID_not)
    {
      return property_obligations_rec(
        to_not_expr(op).op(), solver, current, no_timeframes, ns);
    }
    else if(op.id() == ID_sva_until)
    {
      // ¬(φ W ψ) ≡ (¬φ strongR ¬ψ)
      auto &W = to_sva_until_expr(op);
      auto strong_R = strong_R_exprt{not_exprt{W.lhs()}, not_exprt{W.rhs()}};
      return property_obligations_rec(
        strong_R, solver, current, no_timeframes, ns);
    }
    else if(op.id() == ID_sva_s_until)
    {
      // ¬(φ U ψ) ≡ (¬φ R ¬ψ)
      auto &U = to_sva_s_until_expr(op);
      auto R = R_exprt{not_exprt{U.lhs()}, not_exprt{U.rhs()}};
      return property_obligations_rec(R, solver, current, no_timeframes, ns);
    }
    else if(op.id() == ID_sva_until_with)
    {
      // ¬(φ R ψ) ≡ (¬φ U ¬ψ)
      // Note LHS and RHS are swapped.
      auto &until_with = to_sva_until_with_expr(op);
      auto R = R_exprt{until_with.rhs(), until_with.lhs()};
      auto U = sva_until_exprt{not_exprt{R.lhs()}, not_exprt{R.rhs()}};
      return property_obligations_rec(U, solver, current, no_timeframes, ns);
    }
    else if(op.id() == ID_sva_s_until_with)
    {
      // ¬(φ strongR ψ) ≡ (¬φ W ¬ψ)
      // Note LHS and RHS are swapped.
      auto &s_until_with = to_sva_s_until_with_expr(op);
      auto strong_R = strong_R_exprt{s_until_with.rhs(), s_until_with.lhs()};
      auto W =
        weak_U_exprt{not_exprt{strong_R.lhs()}, not_exprt{strong_R.rhs()}};
      return property_obligations_rec(W, solver, current, no_timeframes, ns);
    }
    else
      return obligationst{
        instantiate_property(property_expr, current, no_timeframes, ns)};
  }
  else
  {
    return obligationst{
      instantiate_property(property_expr, current, no_timeframes, ns)};
  }
}

/*******************************************************************\

Function: property_obligations

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

obligationst property_obligations(
  const exprt &property_expr,
  decision_proceduret &solver,
  const mp_integer &no_timeframes,
  const namespacet &ns)
{
  return property_obligations_rec(property_expr, solver, 0, no_timeframes, ns);
}

/*******************************************************************\

Function: property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void property(
  const exprt &property_expr,
  exprt::operandst &prop_handles,
  message_handlert &message_handler,
  decision_proceduret &solver,
  std::size_t no_timeframes,
  const namespacet &ns)
{
  // The first element of the pair is the length of the
  // counterexample, and the second is the condition that
  // must be valid for the property to hold.
  auto obligations =
    property_obligations(property_expr, solver, no_timeframes, ns);

  // Map obligations onto timeframes.
  prop_handles.resize(no_timeframes, true_exprt());
  for(auto &obligation_it : obligations.map)
  {
    auto t = obligation_it.first;
    DATA_INVARIANT(
      t >= 0 && t < no_timeframes, "obligation must have valid timeframe");
    auto t_int = numeric_cast_v<std::size_t>(t);
    prop_handles[t_int] = solver.handle(conjunction(obligation_it.second));
  }
}
