/*******************************************************************\

Module: Linear Encoding of Lasso-Shaped Counterexamples

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "ltl_linear_lasso.h"

#include <util/arith_tools.h>
#include <util/irep_hash.h>
#include <util/std_expr.h>

#include <temporal-logic/ctl.h>
#include <temporal-logic/ltl.h>
#include <temporal-logic/nnf.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

#include "instantiate_word_level.h"
#include "lasso.h"

#include <unordered_map>

// The paths considered are lassos s_0 ... s_k where the state s_k is
// equal to the state s_j for some j<k chosen by the loop selector
// variables. The successor of s_k on the infinite path is s_{j+1}.
// Hence, every timeframe 0..k is a position on the infinite path,
// and position k+1 is equal to timeframe j+1.
//
// For each subformula ψ, we compute the truth value [[ψ]]_i of ψ at
// position i for i=0..k+1. The value at position k+1 is obtained by
// selecting the value [[ψ]]_{j+1} using the loop selectors.
//
// This is circular for the fixed-point operators (U, R, and the
// derived operators F, G, W, strong R). For these, we follow the
// second-lap approximation of Biere et al.: the value at position k+1
// (i.e., in timeframe j+1) is computed using an auxiliary chain
// <<ψ>>_i over i=j+1..k that uses the values of the operands, which
// are exact, and which ends with the value of the fixed point that
// applies when the eventuality is never fulfilled. One lap suffices,
// since the operands repeat with the period of the loop.
//
// All values are passed through solver.handle(...), which keeps each
// value small, and the encoding is linear in k and in the size of the
// property.

// The largest bound of a ranged SVA operator that we expand
static const mp_integer max_range = 256;

static bool is_boolean_sequence(const exprt &sequence)
{
  return sequence.id() == ID_sva_boolean &&
         !has_temporal_operator(to_sva_boolean_expr(sequence).op());
}

static bool is_sequence_property(const exprt &expr)
{
  return expr.id() == ID_sva_strong || expr.id() == ID_sva_weak ||
         expr.id() == ID_sva_implicit_strong ||
         expr.id() == ID_sva_implicit_weak;
}

// get the constant bounds of a ranged SVA operator
static bool
get_range(const exprt &expr, mp_integer &from, std::optional<mp_integer> &to)
{
  auto &ranged = to_sva_ranged_predicate_exprt(expr);
  auto from_opt = numeric_cast<mp_integer>(ranged.from());
  if(!from_opt.has_value() || *from_opt < 0 || *from_opt > max_range)
    return false;
  from = *from_opt;

  if(!ranged.is_range())
    return false;
  else if(ranged.is_unbounded())
  {
    to = {};
  }
  else
  {
    auto to_opt = numeric_cast<mp_integer>(ranged.to());
    if(!to_opt.has_value() || *to_opt < from || *to_opt > max_range)
      return false;
    to = *to_opt;
  }

  return true;
}

bool ltl_linear_lasso_supported(const exprt &expr)
{
  auto id = expr.id();

  if(
    id == ID_and || id == ID_or || id == ID_implies || id == ID_sva_implies ||
    id == ID_sva_iff)
  {
    for(auto &op : expr.operands())
      if(!ltl_linear_lasso_supported(op))
        return false;
    return true;
  }
  else if(id == ID_equal && to_equal_expr(expr).lhs().type().id() == ID_bool)
  {
    return ltl_linear_lasso_supported(to_equal_expr(expr).lhs()) &&
           ltl_linear_lasso_supported(to_equal_expr(expr).rhs());
  }
  else if(
    id == ID_typecast && to_typecast_expr(expr).op().type().id() == ID_bool)
  {
    return ltl_linear_lasso_supported(to_typecast_expr(expr).op());
  }
  else if(id == ID_if)
  {
    auto &if_expr = to_if_expr(expr);
    return !has_temporal_operator(if_expr.cond()) &&
           ltl_linear_lasso_supported(if_expr.true_case()) &&
           ltl_linear_lasso_supported(if_expr.false_case());
  }
  else if(id == ID_not)
  {
    auto &op = to_not_expr(expr).op();
    auto negated_opt = negate_property_node(op);
    if(negated_opt.has_value())
      return ltl_linear_lasso_supported(*negated_opt);
    else
      return !has_temporal_operator(op);
  }
  else if(
    id == ID_G || id == ID_AG || id == ID_sva_always || id == ID_F ||
    id == ID_AF || id == ID_sva_s_eventually || id == ID_X || id == ID_AX ||
    id == ID_sva_nexttime || id == ID_sva_s_nexttime)
  {
    return ltl_linear_lasso_supported(to_unary_expr(expr).op());
  }
  else if(
    id == ID_U || id == ID_weak_U || id == ID_R || id == ID_strong_R ||
    id == ID_sva_until || id == ID_sva_s_until || id == ID_sva_until_with ||
    id == ID_sva_s_until_with)
  {
    return ltl_linear_lasso_supported(to_binary_expr(expr).lhs()) &&
           ltl_linear_lasso_supported(to_binary_expr(expr).rhs());
  }
  else if(
    id == ID_sva_ranged_always || id == ID_sva_s_always ||
    id == ID_sva_eventually || id == ID_sva_ranged_s_eventually)
  {
    mp_integer from;
    std::optional<mp_integer> to;
    if(!get_range(expr, from, to))
      return false;
    // the weak eventually and s_always require bounded ranges
    if(!to.has_value() && (id == ID_sva_eventually || id == ID_sva_s_always))
    {
      return false;
    }
    return ltl_linear_lasso_supported(to_sva_ranged_predicate_exprt(expr).op());
  }
  else if(
    id == ID_sva_overlapped_followed_by ||
    id == ID_sva_nonoverlapped_followed_by)
  {
    auto &followed_by = to_sva_followed_by_expr(expr);
    return is_boolean_sequence(followed_by.antecedent()) &&
           ltl_linear_lasso_supported(followed_by.consequent());
  }
  else if(
    id == ID_sva_overlapped_implication ||
    id == ID_sva_non_overlapped_implication)
  {
    auto &implication = to_binary_expr(expr);
    return is_boolean_sequence(implication.lhs()) &&
           ltl_linear_lasso_supported(implication.rhs());
  }
  else if(is_sequence_property(expr))
  {
    return is_boolean_sequence(
      to_sva_sequence_property_expr_base(expr).sequence());
  }
  else
  {
    // A state predicate. Anything else (sequences, abort operators,
    // past operators, CTL operators beyond the ACTL fragment) is not
    // supported.
    return !has_temporal_operator(expr);
  }
}

class ltl_linear_lassot
{
public:
  ltl_linear_lassot(
    const mp_integer &_no_timeframes,
    decision_proceduret &_solver)
    : no_timeframes(_no_timeframes),
      k(numeric_cast_v<std::size_t>(_no_timeframes) - 1),
      solver(_solver)
  {
    PRECONDITION(k >= 1);
    selectors.reserve(k);
    for(std::size_t j = 0; j < k; j++)
      selectors.push_back(lasso_select_symbol(j, k));
  }

  /// the values of the subformula at positions 0..k+1
  using valuest = std::vector<exprt>;

  const valuest &values(const exprt &);

  exprt loop_exists() const
  {
    return disjunction(exprt::operandst{selectors.begin(), selectors.end()});
  }

protected:
  const mp_integer no_timeframes;
  const std::size_t k;
  decision_proceduret &solver;
  std::vector<symbol_exprt> selectors;
  std::unordered_map<exprt, valuest, irep_hash> cache;

  valuest compute(const exprt &);

  exprt handle(const exprt &expr)
  {
    if(expr.is_constant())
      return expr;
    else
      return solver.handle(expr);
  }

  static exprt make_and(const exprt &a, const exprt &b)
  {
    if(a.is_false() || b.is_false())
      return false_exprt{};
    else if(a.is_true())
      return b;
    else if(b.is_true())
      return a;
    else
      return and_exprt{a, b};
  }

  static exprt make_or(const exprt &a, const exprt &b)
  {
    if(a.is_true() || b.is_true())
      return true_exprt{};
    else if(a.is_false())
      return b;
    else if(b.is_false())
      return a;
    else
      return or_exprt{a, b};
  }

  /// The value at position k+1, given the values at positions 1..k.
  /// The given vector must have at least k+1 elements.
  exprt loop_value(const valuest &v)
  {
    exprt::operandst disjuncts;
    disjuncts.reserve(k);
    for(std::size_t j = 0; j < k; j++)
    {
      auto conjunct = make_and(selectors[j], v[j + 1]);
      if(!conjunct.is_false())
        disjuncts.push_back(conjunct);
    }
    return handle(disjunction(disjuncts));
  }

  valuest state_predicate(const exprt &);
  valuest next(const valuest &);
  valuest
  fixed_point(const valuest &p, const valuest &q, bool until, bool weak);
  valuest X_power(const exprt &, const mp_integer &);
};

ltl_linear_lassot::valuest ltl_linear_lassot::state_predicate(const exprt &expr)
{
  valuest result;
  result.reserve(k + 2);
  for(std::size_t i = 0; i <= k; i++)
    result.push_back(
      handle(instantiate_state_predicate(expr, i, no_timeframes)));
  result.push_back(loop_value(result));
  return result;
}

ltl_linear_lassot::valuest ltl_linear_lassot::next(const valuest &op)
{
  // [[X ψ]]_i = [[ψ]]_{i+1}
  valuest result;
  result.reserve(k + 2);
  for(std::size_t i = 0; i <= k; i++)
    result.push_back(op[i + 1]);
  result.push_back(loop_value(result));
  return result;
}

/// until=true: p U q (weak=false) or p W q (weak=true)
///   [[ψ]]_i = [[q]]_i ∨ ([[p]]_i ∧ [[ψ]]_{i+1})
/// until=false: p R q (weak=true) or p strongR q (weak=false)
///   [[ψ]]_i = [[q]]_i ∧ ([[p]]_i ∨ [[ψ]]_{i+1})
/// When the eventuality is never fulfilled, the value is true for the
/// weak variants and false for the strong variants.
ltl_linear_lassot::valuest ltl_linear_lassot::fixed_point(
  const valuest &p,
  const valuest &q,
  bool until,
  bool weak)
{
  auto step = [&](std::size_t i, const exprt &next) -> exprt
  {
    if(until)
      return handle(make_or(q[i], make_and(p[i], next)));
    else
      return handle(make_and(q[i], make_or(p[i], next)));
  };

  // the second lap, <<ψ>>_i for i=1..k
  valuest second_lap(k + 2);
  second_lap[k + 1] = weak ? exprt{true_exprt{}} : exprt{false_exprt{}};
  for(std::size_t i = k; i >= 1; i--)
    second_lap[i] = step(i, second_lap[i + 1]);

  // the first lap
  valuest result(k + 2);
  result[k + 1] = loop_value(second_lap);
  for(std::size_t i = k + 1; i-- > 0;)
    result[i] = step(i, result[i + 1]);

  return result;
}

/// The values of X^n ψ
ltl_linear_lassot::valuest
ltl_linear_lassot::X_power(const exprt &op, const mp_integer &n)
{
  exprt tmp = op;
  for(mp_integer i = 0; i < n; ++i)
    tmp = X_exprt{tmp};
  return values(tmp);
}

const ltl_linear_lassot::valuest &ltl_linear_lassot::values(const exprt &expr)
{
  auto it = cache.find(expr);
  if(it != cache.end())
    return it->second;

  auto result = compute(expr);
  DATA_INVARIANT(result.size() == k + 2, "values for each position");
  return cache.emplace(expr, std::move(result)).first->second;
}

ltl_linear_lassot::valuest ltl_linear_lassot::compute(const exprt &expr)
{
  auto id = expr.id();

  auto pointwise =
    [this](const std::vector<const valuest *> &operands, bool is_and) -> valuest
  {
    valuest result;
    result.reserve(k + 2);
    for(std::size_t i = 0; i < k + 2; i++)
    {
      exprt tmp = is_and ? exprt{true_exprt{}} : exprt{false_exprt{}};
      for(auto op : operands)
        tmp = is_and ? make_and(tmp, (*op)[i]) : make_or(tmp, (*op)[i]);
      result.push_back(handle(tmp));
    }
    return result;
  };

  if(id == ID_and || id == ID_or)
  {
    std::vector<valuest> operand_values;
    operand_values.reserve(expr.operands().size());
    for(auto &op : expr.operands())
      operand_values.push_back(values(op));
    std::vector<const valuest *> operands;
    for(auto &v : operand_values)
      operands.push_back(&v);
    return pointwise(operands, id == ID_and);
  }
  else if(id == ID_implies || id == ID_sva_implies)
  {
    auto &binary = to_binary_expr(expr);
    return values(or_exprt{not_exprt{binary.lhs()}, binary.rhs()});
  }
  else if(id == ID_sva_iff)
  {
    auto &binary = to_binary_expr(expr);
    return values(equal_exprt{binary.lhs(), binary.rhs()});
  }
  else if(id == ID_equal && to_equal_expr(expr).lhs().type().id() == ID_bool)
  {
    // a<=>b ---> a=>b && b=>a, which yields NNF
    auto &equal_expr = to_equal_expr(expr);
    return values(and_exprt{
      implies_exprt{equal_expr.lhs(), equal_expr.rhs()},
      implies_exprt{equal_expr.rhs(), equal_expr.lhs()}});
  }
  else if(
    id == ID_typecast && to_typecast_expr(expr).op().type().id() == ID_bool)
  {
    return values(to_typecast_expr(expr).op());
  }
  else if(id == ID_if)
  {
    auto &if_expr = to_if_expr(expr);
    auto cond = state_predicate(if_expr.cond());
    auto true_case = values(if_expr.true_case());
    auto false_case = values(if_expr.false_case());
    valuest result;
    result.reserve(k + 2);
    for(std::size_t i = 0; i < k + 2; i++)
      result.push_back(handle(if_exprt{cond[i], true_case[i], false_case[i]}));
    return result;
  }
  else if(id == ID_not)
  {
    auto &op = to_not_expr(expr).op();
    auto negated_opt = negate_property_node(op);
    if(negated_opt.has_value())
      return values(*negated_opt);
    else
      return state_predicate(expr);
  }
  else if(id == ID_G || id == ID_AG || id == ID_sva_always)
  {
    // G ψ ≡ false R ψ
    auto op = values(to_unary_expr(expr).op());
    valuest false_values(k + 2, false_exprt{});
    return fixed_point(false_values, op, false, true);
  }
  else if(id == ID_F || id == ID_AF || id == ID_sva_s_eventually)
  {
    // F ψ ≡ true U ψ
    auto op = values(to_unary_expr(expr).op());
    valuest true_values(k + 2, true_exprt{});
    return fixed_point(true_values, op, true, false);
  }
  else if(
    id == ID_X || id == ID_AX || id == ID_sva_nexttime ||
    id == ID_sva_s_nexttime)
  {
    // On infinite paths, weak and strong nexttime agree.
    auto op = values(to_unary_expr(expr).op());
    return next(op);
  }
  else if(
    id == ID_U || id == ID_weak_U || id == ID_sva_s_until || id == ID_sva_until)
  {
    auto p = values(to_binary_expr(expr).lhs());
    auto q = values(to_binary_expr(expr).rhs());
    bool weak = id == ID_weak_U || id == ID_sva_until;
    return fixed_point(p, q, true, weak);
  }
  else if(id == ID_R || id == ID_strong_R)
  {
    auto p = values(to_binary_expr(expr).lhs());
    auto q = values(to_binary_expr(expr).rhs());
    return fixed_point(p, q, false, id == ID_R);
  }
  else if(id == ID_sva_until_with || id == ID_sva_s_until_with)
  {
    // φ until_with ψ ≡ ψ R φ, and the strong variant is strong R.
    // Note that lhs and rhs are flipped.
    auto p = values(to_binary_expr(expr).rhs());
    auto q = values(to_binary_expr(expr).lhs());
    return fixed_point(p, q, false, id == ID_sva_until_with);
  }
  else if(
    id == ID_sva_ranged_always || id == ID_sva_s_always ||
    id == ID_sva_eventually || id == ID_sva_ranged_s_eventually)
  {
    mp_integer from;
    std::optional<mp_integer> to;
    bool ok = get_range(expr, from, to);
    INVARIANT(ok, "range must be supported");
    auto &op = to_sva_ranged_predicate_exprt(expr).op();

    // On infinite paths, the weak and strong variants agree.
    bool is_always = id == ID_sva_ranged_always || id == ID_sva_s_always;

    if(!to.has_value())
    {
      // [from:$]
      if(is_always)
        return X_power(G_exprt{op}, from);
      else
        return X_power(F_exprt{op}, from);
    }

    std::vector<valuest> operand_values;
    for(mp_integer i = from; i <= *to; ++i)
      operand_values.push_back(X_power(op, i));
    std::vector<const valuest *> operands;
    for(auto &v : operand_values)
      operands.push_back(&v);
    return pointwise(operands, is_always);
  }
  else if(
    id == ID_sva_overlapped_followed_by ||
    id == ID_sva_nonoverlapped_followed_by)
  {
    // The antecedent is a Boolean; it does not match empty.
    // a #-# p ≡ a ∧ p, a #=# p ≡ a ∧ X p
    auto &followed_by = to_sva_followed_by_expr(expr);
    auto &a = to_sva_boolean_expr(followed_by.antecedent()).op();
    auto &p = followed_by.consequent();
    if(id == ID_sva_overlapped_followed_by)
      return values(and_exprt{a, p});
    else
      return values(and_exprt{a, X_exprt{p}});
  }
  else if(
    id == ID_sva_overlapped_implication ||
    id == ID_sva_non_overlapped_implication)
  {
    // The antecedent is a Boolean; it does not match empty.
    // a |-> p ≡ ¬a ∨ p, a |=> p ≡ ¬a ∨ X p
    auto &implication = to_binary_expr(expr);
    auto &a = to_sva_boolean_expr(implication.lhs()).op();
    auto &p = implication.rhs();
    if(id == ID_sva_overlapped_implication)
      return values(or_exprt{not_exprt{a}, p});
    else
      return values(or_exprt{not_exprt{a}, X_exprt{p}});
  }
  else if(is_sequence_property(expr))
  {
    // A Boolean sequence. Weak and strong agree on infinite paths.
    auto &sequence = to_sva_sequence_property_expr_base(expr).sequence();
    return state_predicate(to_sva_boolean_expr(sequence).op());
  }
  else
  {
    INVARIANT(!has_temporal_operator(expr), "expected state predicate");
    return state_predicate(expr);
  }
}

exprt ltl_linear_lasso_obligation(
  const exprt &property_expr,
  const mp_integer &no_timeframes,
  decision_proceduret &solver)
{
  // A lasso requires at least two timeframes.
  if(no_timeframes < 2)
    return true_exprt{};

  ltl_linear_lassot ltl_linear_lasso{no_timeframes, solver};

  auto &values = ltl_linear_lasso.values(property_expr);

  // The loop selectors are kept outside of the handles,
  // to make them visible to uses_lasso_symbol.
  return implies_exprt{ltl_linear_lasso.loop_exists(), values[0]};
}
