/*******************************************************************\

Module: Negation Normal Form for temporal logic

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "nnf.h"

#include <verilog/sva_expr.h>

#include "temporal_expr.h"

std::optional<exprt> negate_property_node(const exprt &expr)
{
  if(expr.id() == ID_U)
  {
    // ¬(φ U ψ) ≡ (¬φ R ¬ψ)
    auto &U = to_U_expr(expr);
    return R_exprt{not_exprt{U.lhs()}, not_exprt{U.rhs()}};
  }
  else if(expr.id() == ID_R)
  {
    // ¬(φ R ψ) ≡ (¬φ U ¬ψ)
    auto &R = to_R_expr(expr);
    return U_exprt{not_exprt{R.lhs()}, not_exprt{R.rhs()}};
  }
  else if(expr.id() == ID_G)
  {
    // ¬G φ ≡ F ¬φ
    auto &G = to_G_expr(expr);
    return F_exprt{not_exprt{G.op()}};
  }
  else if(expr.id() == ID_F)
  {
    // ¬F φ ≡ G ¬φ
    auto &F = to_F_expr(expr);
    return G_exprt{not_exprt{F.op()}};
  }
  else if(expr.id() == ID_X)
  {
    // ¬X φ ≡ X ¬φ
    auto &X = to_X_expr(expr);
    return X_exprt{not_exprt{X.op()}};
  }
  else if(expr.id() == ID_implies)
  {
    // ¬(a->b) ≡ a && ¬b
    auto &implies_expr = to_implies_expr(expr);
    return and_exprt{implies_expr.lhs(), not_exprt{implies_expr.rhs()}};
  }
  else if(expr.id() == ID_and)
  {
    auto operands = expr.operands();
    for(auto &op : operands)
      op = not_exprt{op};
    return or_exprt{std::move(operands)};
  }
  else if(expr.id() == ID_or)
  {
    auto operands = expr.operands();
    for(auto &op : operands)
      op = not_exprt{op};
    return and_exprt{std::move(operands)};
  }
  else if(expr.id() == ID_not)
  {
    return to_not_expr(expr).op();
  }
  else if(expr.id() == ID_sva_always)
  {
    // not always p --> s_eventually not p
    return sva_s_eventually_exprt{not_exprt{to_sva_always_expr(expr).op()}};
  }
  else if(expr.id() == ID_sva_ranged_always)
  {
    // not always [x:y] p --> s_eventually [x:y] not p
    auto &always = to_sva_ranged_always_expr(expr);
    return sva_ranged_s_eventually_exprt{
      always.lower(), always.upper(), not_exprt{always.op()}};
  }
  else if(expr.id() == ID_sva_s_eventually)
  {
    // not s_eventually p --> always not p
    return sva_always_exprt{not_exprt{to_sva_s_eventually_expr(expr).op()}};
  }
  else if(expr.id() == ID_sva_eventually)
  {
    // not eventually[i:j] p --> s_always[i:j] not p
    auto &eventually = to_sva_eventually_expr(expr);
    return sva_s_always_exprt{
      eventually.lower(), eventually.upper(), not_exprt{eventually.op()}};
  }
  else if(expr.id() == ID_sva_until)
  {
    // ¬(φ W ψ) ≡ (¬φ strongR ¬ψ)
    auto &W = to_sva_until_expr(expr);
    return strong_R_exprt{not_exprt{W.lhs()}, not_exprt{W.rhs()}};
  }
  else if(expr.id() == ID_sva_s_until)
  {
    // ¬(φ U ψ) ≡ (¬φ R ¬ψ)
    auto &U = to_sva_s_until_expr(expr);
    return R_exprt{not_exprt{U.lhs()}, not_exprt{U.rhs()}};
  }
  else if(expr.id() == ID_sva_until_with)
  {
    // ¬(φ R ψ) ≡ (¬φ U ¬ψ)
    // Note LHS and RHS are swapped.
    auto &until_with = to_sva_until_with_expr(expr);
    auto R = R_exprt{until_with.rhs(), until_with.lhs()};
    return sva_until_exprt{not_exprt{R.lhs()}, not_exprt{R.rhs()}};
  }
  else if(expr.id() == ID_sva_s_until_with)
  {
    // ¬(φ strongR ψ) ≡ (¬φ W ¬ψ)
    // Note LHS and RHS are swapped.
    auto &s_until_with = to_sva_s_until_with_expr(expr);
    auto strong_R = strong_R_exprt{s_until_with.rhs(), s_until_with.lhs()};
    return weak_U_exprt{not_exprt{strong_R.lhs()}, not_exprt{strong_R.rhs()}};
  }
  else if(expr.id() == ID_sva_overlapped_followed_by)
  {
    // 1800 2017 16.12.9
    // !(a #-# b)   --->   a |-> !b
    auto &followed_by = to_sva_followed_by_expr(expr);
    auto not_b = not_exprt{followed_by.property()};
    return sva_overlapped_implication_exprt{followed_by.lhs(), not_b};
  }
  else if(expr.id() == ID_sva_nonoverlapped_followed_by)
  {
    // 1800 2017 16.12.9
    // !(a #=# b)   --->   a |=> !b
    auto &followed_by = to_sva_followed_by_expr(expr);
    auto not_b = not_exprt{followed_by.property()};
    return sva_non_overlapped_implication_exprt{followed_by.lhs(), not_b};
  }
  else
    return {};
}

exprt property_nnf(exprt expr)
{
  // Do the node
  if(expr.id() == ID_not)
  {
    auto node_opt = negate_property_node(to_not_expr(expr).op());
    if(!node_opt.has_value())
      return expr; // give up

    expr = node_opt.value();
  }
  else if(expr.id() == ID_implies)
  {
    auto &implies = to_implies_expr(expr);
    expr = or_exprt{not_exprt{implies.lhs()}, implies.rhs()};
  }
  else if(
    expr.id() == ID_equal && to_equal_expr(expr).lhs().type().id() == ID_bool)
  {
    auto &equal = to_equal_expr(expr);
    expr = and_exprt{
      implies_exprt{equal.lhs(), equal.rhs()},
      implies_exprt{equal.rhs(), equal.lhs()}};
  }

  // Do the operands, recursively
  for(auto &op : expr.operands())
    op = property_nnf(op);

  return expr;
}
