/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "instantiate_word_level.h"

#include <util/ebmc_util.h>

#include <temporal-logic/temporal_expr.h>
#include <verilog/sva_expr.h>

#include "property.h"

#include <cassert>

/*******************************************************************\

Function: timeframe_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string
timeframe_identifier(const mp_integer &timeframe, const irep_idt &identifier)
{
  return id2string(identifier) + "@" + integer2string(timeframe);
}

/*******************************************************************\

Function: timeframe_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt timeframe_symbol(const mp_integer &timeframe, symbol_exprt src)
{
  auto result = std::move(src);
  result.set_identifier(
    timeframe_identifier(timeframe, result.get_identifier()));
  return result;
}

/*******************************************************************\

   Class: wl_instantiatet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class wl_instantiatet
{
public:
  wl_instantiatet(const mp_integer &_no_timeframes, const namespacet &_ns)
    : no_timeframes(_no_timeframes), ns(_ns)
  {
  }

  /// Instantiate the given expression for timeframe t
  [[nodiscard]] exprt operator()(exprt expr, const mp_integer &t) const
  {
    return instantiate_rec(std::move(expr), t);
  }

protected:
  const mp_integer &no_timeframes;
  const namespacet &ns;

  [[nodiscard]] exprt instantiate_rec(exprt, const mp_integer &t) const;
  [[nodiscard]] typet instantiate_rec(typet, const mp_integer &t) const;
};

/*******************************************************************\

Function: wl_instantiatet::instantiate_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt wl_instantiatet::instantiate_rec(exprt expr, const mp_integer &t) const
{
  expr.type() = instantiate_rec(expr.type(), t);

  if(expr.id() == ID_next_symbol)
  {
    expr.id(ID_symbol);
    return timeframe_symbol(t + 1, to_symbol_expr(std::move(expr)));
  }
  else if(expr.id() == ID_symbol)
  {
    return timeframe_symbol(t, to_symbol_expr(std::move(expr)));
  }
  else if(expr.id()==ID_sva_cycle_delay) // ##[1:2] something
  {
    auto &sva_cycle_delay_expr = to_sva_cycle_delay_expr(expr);

    if(sva_cycle_delay_expr.to().is_nil())
    {
      mp_integer offset;
      if(to_integer_non_constant(sva_cycle_delay_expr.from(), offset))
        throw "failed to convert sva_cycle_delay offset";

      const auto u = t + offset;

      // Do we exceed the bound? Make it 'true'
      if(u >= no_timeframes)
        return true_exprt();
      else
        return instantiate_rec(sva_cycle_delay_expr.op(), u);
    }
    else
    {
      mp_integer from, to;
      if(to_integer_non_constant(sva_cycle_delay_expr.from(), from))
        throw "failed to convert sva_cycle_delay offsets";

      if(sva_cycle_delay_expr.to().id() == ID_infinity)
      {
        assert(no_timeframes != 0);
        to = no_timeframes - 1;
      }
      else if(to_integer_non_constant(sva_cycle_delay_expr.to(), to))
        throw "failed to convert sva_cycle_delay offsets";

      // This is an 'or', and we let it fail if the bound is too small.

      exprt::operandst disjuncts;

      for(mp_integer offset = from; offset < to; ++offset)
      {
        auto u = t + offset;

        if(u >= no_timeframes)
        {
        }
        else
        {
          disjuncts.push_back(instantiate_rec(sva_cycle_delay_expr.op(), u));
        }
      }

      return disjunction(disjuncts);
    }
  }
  else if(expr.id()==ID_sva_sequence_concatenation)
  {
    // much like regular 'and'
    expr.id(ID_and);

    for(auto &op : expr.operands())
      op = instantiate_rec(op, t);

    return expr;
  }
  else if(expr.id()==ID_sva_always)
  {
    auto &op = to_sva_always_expr(expr).op();

    exprt::operandst conjuncts;

    for(auto u = t; u < no_timeframes; ++u)
    {
      conjuncts.push_back(instantiate_rec(op, u));
    }

    return conjunction(conjuncts);
  }
  else if(expr.id() == ID_X)
  {
    const auto next = t + 1;

    if(next < no_timeframes)
    {
      return instantiate_rec(to_X_expr(expr).op(), next);
    }
    else
      return true_exprt(); // works on NNF only
  }
  else if(expr.id() == ID_sva_eventually)
  {
    const auto &eventually_expr = to_sva_eventually_expr(expr);
    const auto &range = eventually_expr.range();
    const auto &op = eventually_expr.op();

    mp_integer lower;
    if(to_integer_non_constant(range.op0(), lower))
      throw "failed to convert sva_eventually index";

    mp_integer upper;
    if(to_integer_non_constant(range.op1(), upper))
      throw "failed to convert sva_eventually index";

    // This is weak, and passes if any of the timeframes
    // does not exist.
    if(t + lower >= no_timeframes || t + upper >= no_timeframes)
      return true_exprt();

    exprt::operandst disjuncts = {};

    for(mp_integer u = t + lower; u <= t + upper; ++u)
      disjuncts.push_back(instantiate_rec(op, u));

    return disjunction(disjuncts);
  }
  else if(
    expr.id() == ID_sva_s_eventually || expr.id() == ID_F || expr.id() == ID_AF)
  {
    const auto &p = to_unary_expr(expr).op();

    // The following needs to be satisfied for a counterexample
    // to Fp:
    // (1) There is a loop from the current state i back to
    //     some earlier state k < i.
    // (1) No state j with k<=k<=i on the lasso satisfies 'p'.
    //
    // We look backwards instead of forwards so that 't'
    // is the last state of the counterexample trace.
    //
    // Note that this is trivially true when t is zero,
    // as a single state cannot demonstrate the loop.

    exprt::operandst conjuncts = {};
    const auto i = t;

    for(mp_integer k = 0; k < i; ++k)
    {
      exprt::operandst disjuncts = {not_exprt(lasso_symbol(k, i))};

      for(mp_integer j = k; j <= i; ++j)
      {
        disjuncts.push_back(instantiate_rec(p, j));
      }

      conjuncts.push_back(disjunction(disjuncts));
    }

    return conjunction(conjuncts);
  }
  else if(expr.id()==ID_sva_until ||
          expr.id()==ID_sva_s_until)
  {
    // non-overlapping until
  
    assert(expr.operands().size()==2);
    
    // we need a lasso to refute these

    // we expand: p U q <=> q || (p && X(p U q))
    exprt tmp_q = to_binary_expr(expr).op1();
    tmp_q = instantiate_rec(tmp_q, t);

    exprt expansion = to_binary_expr(expr).op0();
    expansion = instantiate_rec(expansion, t);

    const auto next = t + 1;

    if(next < no_timeframes)
    {
      expansion = and_exprt(expansion, instantiate_rec(expr, next));
    }

    return or_exprt(tmp_q, expansion);
  }
  else if(expr.id()==ID_sva_until_with ||
          expr.id()==ID_sva_s_until_with)
  {
    // overlapping until
  
    assert(expr.operands().size()==2);
    
    // we rewrite using 'next'
    binary_exprt tmp = to_binary_expr(expr);
    if(expr.id()==ID_sva_until_with)
      tmp.id(ID_sva_until);
    else
      tmp.id(ID_sva_s_until);

    tmp.op1() = X_exprt(tmp.op1());

    return instantiate_rec(tmp, t);
  }
  else
  {
    for(auto &op : expr.operands())
      op = instantiate_rec(op, t);
    return expr;
  }
}

/*******************************************************************\

Function: wl_instantiatet::instantiate_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet wl_instantiatet::instantiate_rec(typet type, const mp_integer &) const
{
  return type;
}

/*******************************************************************\

Function: instantiate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt instantiate(
  const exprt &expr,
  const mp_integer &t,
  const mp_integer &no_timeframes,
  const namespacet &ns)
{
  wl_instantiatet wl_instantiate(no_timeframes, ns);
  return wl_instantiate(expr, t);
}
