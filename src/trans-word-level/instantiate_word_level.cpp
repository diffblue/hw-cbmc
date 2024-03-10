/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "instantiate_word_level.h"

#include <util/ebmc_util.h>

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
timeframe_identifier(std::size_t timeframe, const irep_idt &identifier)
{
  return id2string(identifier)+"@"+std::to_string(timeframe);
}

/*******************************************************************\

Function: timeframe_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt timeframe_symbol(std::size_t timeframe, symbol_exprt src)
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
  wl_instantiatet(std::size_t _no_timeframes, const namespacet &_ns)
    : no_timeframes(_no_timeframes), ns(_ns)
  {
  }

  /// Instantiate the given expression for timeframe t
  [[nodiscard]] exprt operator()(exprt expr, std::size_t t) const
  {
    return instantiate_rec(std::move(expr), t);
  }

protected:
  std::size_t no_timeframes;
  const namespacet &ns;

  [[nodiscard]] exprt instantiate_rec(exprt, std::size_t t) const;
  [[nodiscard]] typet instantiate_rec(typet, std::size_t t) const;
};

/*******************************************************************\

Function: wl_instantiatet::instantiate_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt wl_instantiatet::instantiate_rec(exprt expr, const std::size_t t) const
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
  else if(expr.id()==ID_sva_overlapped_implication)
  {
    // same as regular implication
    expr.id(ID_implies);

    for(auto &op : expr.operands())
      op = instantiate_rec(op, t);

    return expr;
  }
  else if(expr.id()==ID_sva_non_overlapped_implication)
  {
    // right-hand side is shifted by one tick
    if(expr.operands().size()==2)
    {
      expr.id(ID_implies);
      auto &implies_expr = to_implies_expr(expr);
      implies_expr.op0() = instantiate_rec(implies_expr.op0(), t);

      const auto next = t + 1;

      // Do we exceed the bound? Make it 'true',
      // works on NNF only
      if(next >= no_timeframes)
        implies_expr.op1() = true_exprt();
      else
        implies_expr.op1() = instantiate_rec(implies_expr.op1(), next);

      return std::move(implies_expr);
    }
    else
      return expr;
  }
  else if(expr.id()==ID_sva_cycle_delay) // ##[1:2] something
  {
    if(expr.operands().size()==3)
    {
      auto &ternary_expr = to_ternary_expr(expr);

      if(ternary_expr.op1().is_nil())
      {
        mp_integer offset;
        if(to_integer_non_constant(ternary_expr.op0(), offset))
          throw "failed to convert sva_cycle_delay offset";

        const auto u = t + offset.to_ulong();

        // Do we exceed the bound? Make it 'true'
        if(u >= no_timeframes)
          return true_exprt();
        else
          return instantiate_rec(ternary_expr.op2(), u);
      }
      else
      {
        mp_integer from, to;
        if(to_integer_non_constant(ternary_expr.op0(), from))
          throw "failed to convert sva_cycle_delay offsets";

        if(ternary_expr.op1().id() == ID_infinity)
        {
          assert(no_timeframes!=0);
          to=no_timeframes-1;
        }
        else if(to_integer_non_constant(ternary_expr.op1(), to))
          throw "failed to convert sva_cycle_delay offsets";
          
        // This is an 'or', and we let it fail if the bound is too small.
        
        exprt::operandst disjuncts;
        
        for(mp_integer offset=from; offset<to; ++offset)
        {
          auto u = t + offset.to_ulong();

          if(u >= no_timeframes)
          {
          }
          else
          {
            disjuncts.push_back(instantiate_rec(ternary_expr.op2(), u));
          }
        }

        return disjunction(disjuncts);
      }
    }
    else
      return expr;
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

    for(auto u = t; u < no_timeframes; u++)
    {
      conjuncts.push_back(instantiate_rec(op, u));
    }

    return conjunction(conjuncts);
  }
  else if(expr.id()==ID_sva_nexttime ||
          expr.id()==ID_sva_s_nexttime)
  {
    assert(expr.operands().size()==1);

    const auto next = t + 1;

    if(next < no_timeframes)
    {
      return instantiate_rec(to_unary_expr(expr).op(), next);
    }
    else
      return true_exprt(); // works on NNF only
  }
  else if(
    expr.id() == ID_sva_eventually || expr.id() == ID_sva_s_eventually ||
    expr.id() == ID_F || expr.id() == ID_AF)
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

    for(std::size_t k = 0; k < i; k++)
    {
      exprt::operandst disjuncts = {not_exprt(lasso_symbol(k, i))};

      for(std::size_t j = k; j <= i; j++)
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

    tmp.op1() = sva_nexttime_exprt(tmp.op1());

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

typet wl_instantiatet::instantiate_rec(typet type, std::size_t) const
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
  std::size_t t,
  std::size_t no_timeframes,
  const namespacet &ns)
{
  wl_instantiatet wl_instantiate(no_timeframes, ns);
  return wl_instantiate(expr, t);
}
