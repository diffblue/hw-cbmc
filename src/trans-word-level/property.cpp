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
  // We support
  // * formulas that contain no temporal operator besides X
  // * Gφ, where φ contains no temporal operator besides X
  // * Fφ, where φ contains no temporal operator besides X
  // * GFφ, where φ contains no temporal operator besides X
  // * conjunctions of supported LTL properties
  auto non_X_LTL_operator = [](const exprt &expr)
  { return is_LTL_operator(expr) && expr.id() != ID_X; };

  if(!has_subexpr(expr, non_X_LTL_operator))
  {
    return true;
  }
  else if(expr.id() == ID_F)
  {
    return !has_subexpr(to_F_expr(expr).op(), non_X_LTL_operator);
  }
  else if(expr.id() == ID_G)
  {
    auto &op = to_G_expr(expr).op();
    if(op.id() == ID_F)
    {
      return !has_subexpr(to_F_expr(op).op(), non_X_LTL_operator);
    }
    else
    {
      return !has_subexpr(op, non_X_LTL_operator);
    }
  }
  else if(expr.id() == ID_and)
  {
    for(auto &op : expr.operands())
      if(!bmc_supports_LTL_property(op))
        return false;
    return true;
  }
  else
    return false;
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
  if(!is_temporal_operator(expr))
  {
    if(!has_temporal_operator(expr))
      return true; // initial state only
    else if(
      expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_implies)
    {
      for(auto &op : expr.operands())
        if(!bmc_supports_property(op))
          return false;
      return true;
    }
    else
      return false;
  }
  else if(expr.id() == ID_sva_cycle_delay)
    return !has_temporal_operator(to_sva_cycle_delay_expr(expr).op());
  else if(expr.id() == ID_sva_nexttime)
    return !has_temporal_operator(to_sva_nexttime_expr(expr).op());
  else if(expr.id() == ID_sva_s_nexttime)
    return !has_temporal_operator(to_sva_s_nexttime_expr(expr).op());
  else if(expr.id() == ID_sva_always)
    return true;
  else if(expr.id() == ID_sva_ranged_always)
    return true;
  else if(expr.id() == ID_sva_s_eventually)
    return true;
  else
    return false;
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
  else
    return bmc_supports_SVA_property(expr);
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
  else if(
    property_expr.id() == ID_sva_until || property_expr.id() == ID_sva_s_until)
  {
    // non-overlapping until
    // we need a lasso to refute these

    // we expand: p U q <=> q || (p && X(p U q))
    exprt tmp_q = to_binary_expr(property_expr).op1();
    tmp_q = property_obligations_rec(tmp_q, solver, current, no_timeframes, ns)
              .conjunction()
              .second;

    exprt expansion = to_binary_expr(property_expr).op0();
    expansion =
      property_obligations_rec(expansion, solver, current, no_timeframes, ns)
        .conjunction()
        .second;

    const auto next = current + 1;

    if(next < no_timeframes)
    {
      auto obligations_rec = property_obligations_rec(
        property_expr, solver, next, no_timeframes, ns);
      expansion = and_exprt(expansion, obligations_rec.conjunction().second);
    }

    DATA_INVARIANT(no_timeframes != 0, "must have timeframe");
    return obligationst{no_timeframes - 1, or_exprt(tmp_q, expansion)};
  }
  else if(
    property_expr.id() == ID_sva_until_with ||
    property_expr.id() == ID_sva_s_until_with)
  {
    // overlapping until

    // we rewrite using 'next'
    binary_exprt tmp = to_binary_expr(property_expr);
    if(property_expr.id() == ID_sva_until_with)
      tmp.id(ID_sva_until);
    else
      tmp.id(ID_sva_s_until);

    tmp.op1() = X_exprt{tmp.op1()};

    return property_obligations_rec(tmp, solver, current, no_timeframes, ns);
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

/*******************************************************************\

Function: states_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt states_equal(
  const mp_integer &k,
  const mp_integer &i,
  const std::vector<symbol_exprt> &variables_to_compare)
{
  // We require k<i to avoid the symmetric constraints.
  PRECONDITION(k < i);

  exprt::operandst conjuncts;
  conjuncts.reserve(variables_to_compare.size());

  for(auto &var : variables_to_compare)
  {
    auto i_var = timeframe_symbol(i, var);
    auto k_var = timeframe_symbol(k, var);
    conjuncts.push_back(equal_exprt(i_var, k_var));
  }

  return conjunction(std::move(conjuncts));
}

/*******************************************************************\

Function: lasso_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt lasso_symbol(const mp_integer &k, const mp_integer &i)
{
  // True when states i and k are equal.
  // We require k<i to avoid the symmetric constraints.
  PRECONDITION(k < i);
  irep_idt lasso_identifier =
    "lasso::" + integer2string(i) + "-back-to-" + integer2string(k);
  return symbol_exprt(lasso_identifier, bool_typet());
}

/*******************************************************************\

Function: lasso_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void lasso_constraints(
  decision_proceduret &solver,
  const mp_integer &no_timeframes,
  const namespacet &ns,
  const irep_idt &module_identifier)
{
  // The definition of a lasso to state s_i is that there
  // is an identical state s_k = s_i with k<i.
  // "Identical" is defined as "state variables and top-level inputs match".

  std::vector<symbol_exprt> variables_to_compare;

  // Gather the state variables.
  const symbol_tablet &symbol_table = ns.get_symbol_table();
  auto lower = symbol_table.symbol_module_map.lower_bound(module_identifier);
  auto upper = symbol_table.symbol_module_map.upper_bound(module_identifier);

  for(auto it = lower; it != upper; it++)
  {
    const symbolt &symbol = ns.lookup(it->second);

    if(symbol.is_state_var)
      variables_to_compare.push_back(symbol.symbol_expr());
  }

  // gather the top-level inputs
  const auto &module_symbol = ns.lookup(module_identifier);
  DATA_INVARIANT(module_symbol.type.id() == ID_module, "expected a module");
  const auto &ports = module_symbol.type.find(ID_ports);

  for(auto &port : static_cast<const exprt &>(ports).operands())
  {
    DATA_INVARIANT(port.id() == ID_symbol, "port must be a symbol");
    if(port.get_bool(ID_input) && !port.get_bool(ID_output))
    {
      symbol_exprt input_symbol(port.get(ID_identifier), port.type());
      input_symbol.add_source_location() = port.source_location();
      variables_to_compare.push_back(std::move(input_symbol));
    }
  }

  for(mp_integer i = 1; i < no_timeframes; ++i)
  {
    for(mp_integer k = 0; k < i; ++k)
    {
      // Is there a loop back from time frame i back to time frame k?
      auto lasso_symbol = ::lasso_symbol(k, i);
      auto equal = states_equal(k, i, variables_to_compare);
      solver.set_to_true(equal_exprt(lasso_symbol, equal));
    }
  }
}

/*******************************************************************\

Function: requires_lasso_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool requires_lasso_constraints(const exprt &expr)
{
  for(auto subexpr_it = expr.depth_cbegin(), subexpr_end = expr.depth_cend();
      subexpr_it != subexpr_end;
      subexpr_it++)
  {
    if(
      subexpr_it->id() == ID_sva_until || subexpr_it->id() == ID_sva_s_until ||
      subexpr_it->id() == ID_sva_eventually ||
      subexpr_it->id() == ID_sva_s_eventually || subexpr_it->id() == ID_AF ||
      subexpr_it->id() == ID_F)
    {
      return true;
    }
  }

  return false;
}
