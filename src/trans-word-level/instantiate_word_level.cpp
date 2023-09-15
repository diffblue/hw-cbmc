/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/ebmc_util.h>

#include "instantiate_word_level.h"

/*******************************************************************\

Function: timeframe_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string timeframe_identifier(
  unsigned timeframe,
  const irep_idt &identifier)
{
  return id2string(identifier)+"@"+std::to_string(timeframe);
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
  wl_instantiatet(
    unsigned _current, unsigned _no_timeframes,
    const namespacet &_ns):
    current(_current),
    no_timeframes(_no_timeframes),
    ns(_ns)
  {
  }
  
  inline exprt operator()(const exprt &expr)
  {
    exprt tmp=expr;
    instantiate_rec(tmp);
    return tmp;
  }

protected:
  unsigned current, no_timeframes;
  const namespacet &ns;
  
  void instantiate_rec(exprt &);
  void instantiate_rec(typet &);
  
  class save_currentt
  {
  public:
    inline explicit save_currentt(unsigned &_c):c(_c), saved(c)
    {
    }
    
    inline ~save_currentt()
    {
      c=saved; // restore
    }
    
    unsigned &c, saved;
  };
};

/*******************************************************************\

Function: wl_instantiatet::instantiate_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void wl_instantiatet::instantiate_rec(exprt &expr)
{
  instantiate_rec(expr.type());

  if(expr.id()==ID_next_symbol || expr.id()==ID_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);

    if(expr.id()==ID_next_symbol)
    {
      expr.id(ID_symbol);
      expr.set(ID_identifier, timeframe_identifier(current+1, identifier));
    }
    else
    {
      expr.set(ID_identifier, timeframe_identifier(current, identifier));
    }
  }
  else if(expr.id()==ID_sva_overlapped_implication)
  {
    // same as regular implication
    expr.id(ID_implies);

    Forall_operands(it, expr)
      instantiate_rec(*it);
  }
  else if(expr.id()==ID_sva_non_overlapped_implication)
  {
    // right-hand side is shifted by one tick
    if(expr.operands().size()==2)
    {
      expr.id(ID_implies);
      instantiate_rec(expr.op0());
      
      save_currentt save_current(current);
      
      current++;
      
      // Do we exceed the bound? Make it 'true',
      // works on NNF only
      if(current>=no_timeframes)
        expr.op1()=true_exprt();
      else
        instantiate_rec(expr.op1());
    }
  }
  else if(expr.id()==ID_sva_cycle_delay) // ##[1:2] something
  {
    if(expr.operands().size()==3)
    {
      // save the current time frame, we'll change it
      save_currentt save_current(current);

      if(expr.op1().is_nil())
      {
        mp_integer offset;
        if(to_integer_non_constant(expr.op0(), offset))
          throw "failed to convert sva_cycle_delay offset";

        current = save_current.saved + offset.to_ulong();

        // Do we exceed the bound? Make it 'true'
        if(current>=no_timeframes)
          expr.op2()=true_exprt();
        else
          instantiate_rec(expr.op2());

        expr=expr.op2();
      }
      else
      {
        mp_integer from, to;

        if(to_integer_non_constant(expr.op0(), from))
          throw "failed to convert sva_cycle_delay offsets";
          
        if(expr.op1().id()==ID_infinity)
        {
          assert(no_timeframes!=0);
          to=no_timeframes-1;
        }
        else if(to_integer_non_constant(expr.op1(), to))
          throw "failed to convert sva_cycle_delay offsets";
          
        // This is an 'or', and we let it fail if the bound is too small.
        
        exprt::operandst disjuncts;
        
        for(mp_integer offset=from; offset<to; ++offset)
        {
          current = save_current.saved + offset.to_ulong();

          if(current>=no_timeframes)
          {
          }
          else
          {
            disjuncts.push_back(expr.op2());
            instantiate_rec(disjuncts.back());
          }
        }
        
        expr=disjunction(disjuncts);
      }
    }
  }
  else if(expr.id()==ID_sva_sequence_concatenation)
  {
    // much like regular 'and'
    expr.id(ID_and);
    Forall_operands(it, expr)
      instantiate_rec(*it);
  }
  else if(expr.id()==ID_sva_always)
  {
    assert(expr.operands().size()==1);
    
    // save the current time frame, we'll change it
    save_currentt save_current(current);
    
    exprt::operandst conjuncts;

    for(; current<no_timeframes; current++)
    {
      conjuncts.push_back(expr.op0());
      instantiate_rec(conjuncts.back());
    }
    
    expr=conjunction(conjuncts);
  }
  else if(expr.id()==ID_sva_nexttime ||
          expr.id()==ID_sva_s_nexttime)
  {
    assert(expr.operands().size()==1);
    
    // save the current time frame, we'll change it
    save_currentt save_current(current);
    
    current++;
    
    if(current<no_timeframes)
    {
      expr=expr.op0();
      instantiate_rec(expr);
    }
    else
      expr=true_exprt(); // works on NNF only
  }
  else if(expr.id()==ID_sva_eventually ||
          expr.id()==ID_sva_s_eventually)
  {
    assert(expr.operands().size()==1);
    
    // For Fp to hold, we need one of the following:
    // (1) at least one state from the current point
    //     in time satisfies 'p' OR
    // (2) no state from now on is repeated
    //     (which means 'p' can still hold later)

    // save the current time frame, we'll change it
    
    exprt::operandst disjuncts;

    if(current==0)
    {
      save_currentt save_current(current);
      for(; current<no_timeframes; current++)
      {
        disjuncts.push_back(expr.op0());
        instantiate_rec(disjuncts.back());
      }
      expr=disjunction(disjuncts);
    }
    else
      expr=true_exprt();
  }
  else if(expr.id()==ID_sva_until ||
          expr.id()==ID_sva_s_until)
  {
    // non-overlapping until
  
    assert(expr.operands().size()==2);
    
    // we need a lasso to refute these
    
    // save the current time frame, we'll change it
    save_currentt save_current(current);
    
    // we expand: p U q <=> q || (p && X(p U q))
    exprt tmp_q=expr.op1();
    instantiate_rec(tmp_q);
    
    exprt expansion=expr.op0();
    instantiate_rec(expansion);
    
    current++;
    
    if(current<no_timeframes)
    {
      exprt tmp=expr;
      instantiate_rec(tmp);
      expansion=and_exprt(expansion, tmp);
    }
    
    expr=or_exprt(tmp_q, expansion);
  }
  else if(expr.id()==ID_sva_until_with ||
          expr.id()==ID_sva_s_until_with)
  {
    // overlapping until
  
    assert(expr.operands().size()==2);
    
    // we rewrite using 'next'
    exprt tmp=expr;
    if(expr.id()==ID_sva_until_with)
      tmp.id(ID_sva_until);
    else
      tmp.id(ID_sva_s_until);

    tmp.op1()=unary_predicate_exprt(ID_sva_nexttime, tmp.op1());
    
    instantiate_rec(tmp);
    expr=tmp;
  }
  else
  {
    Forall_operands(it, expr)
      instantiate_rec(*it);
  }
}

/*******************************************************************\

Function: wl_instantiatet::instantiate_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void wl_instantiatet::instantiate_rec(typet &type)
{
}

/*******************************************************************\

Function: instantiate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt instantiate(
  const exprt &expr,
  unsigned current, unsigned no_timeframes,
  const namespacet &ns)
{
  wl_instantiatet wl_instantiate(current, no_timeframes, ns);
  return wl_instantiate(expr);
}
