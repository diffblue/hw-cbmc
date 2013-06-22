/*******************************************************************\

Module: k Induction

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#include <trans/instantiate.h>
#include <trans/property.h>
#include <trans/trans_trace.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/boolbv.h>

#include "ebmc_base.h"
#include "k_induction.h"

/*******************************************************************\

   Class: k_inductiont

 Purpose:

\*******************************************************************/

class k_inductiont:public ebmc_baset
{
public:
  k_inductiont(const cmdlinet &cmdline):ebmc_baset(cmdline)
  {
  }

  int do_k_induction();
  
  int induction_base();
  int induction_step();
};

/*******************************************************************\

Function: do_k_induction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int do_k_induction(const cmdlinet &cmdline)
{
  k_inductiont k_induction(cmdline);
  
  return k_induction.do_k_induction();
}

/*******************************************************************\

Function: k_inductiont::do_k_induction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int k_inductiont::do_k_induction()
{
  if(get_bound()) return 1;

  int result=get_model();
  if(result!=-1) return result;

  if(properties.empty())
  {
    error() << "no properties" << eom;
    return 1;
  }

  // do induction base
  result=induction_base();
  if(result!=-1) return result;

  // do induction step
  result=induction_step();
  return result;
}

/*******************************************************************\

Function: k_inductiont::induction_base

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int k_inductiont::induction_base()
{
  status() << "Induction Base" << eom;

  satcheckt satcheck;
    namespacet ns(symbol_table);
   boolbvt solver(ns, satcheck);

  unwind(solver, bound+1, true);


  property(
    prop_expr_list,
    prop_bv,
    *this, // message
    solver,
    bound+1,
    ns);

  decision_proceduret::resultt dec_result=
    solver.dec_solve();
  
  switch(dec_result)
  {
  case decision_proceduret::D_SATISFIABLE:
    {
      result("SAT: bug found");

      namespacet ns(symbol_table);
      trans_tracet trans_trace;
  
      compute_trans_trace(
        prop_expr_list,
        prop_bv,
        solver,
        bound+1,
        ns,
        main_symbol->name,
        trans_trace);
        
      if(get_ui()==ui_message_handlert::PLAIN)
        result("Counterexample:\n");

      show_trans_trace(
        trans_trace,
        *this, // message
        ns,
        get_ui());
        
      report_failure();
    }
    return 0;

  case decision_proceduret::D_UNSATISFIABLE:
    result("UNSAT: No bug found within bound");
    break;

  case decision_proceduret::D_ERROR:
    error() << "Error from decision procedure" << eom;
    return 2;

  default:
    error() << "Unexpected result from decision procedure" << eom;
    return 1;
  }

  return -1;
}

/*******************************************************************\

Function: k_inductiont::induction_step

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int k_inductiont::induction_step()
{
  status() << "Induction Step" << eom;

  namespacet ns(symbol_table);
  satcheckt satcheck;
  boolbvt solver(ns, satcheck);
  
  unsigned no_timeframes=bound+1;

  // *no* initial state
  unwind(solver, no_timeframes, false);


  for(std::list<propertyt>::const_iterator
      it=properties.begin();
      it!=properties.end();
      it++)
  {
    if(it->expr.is_true())
      continue;
  
    exprt property(it->expr);

    if(property.id()!="AG" ||
       property.operands().size()!=1)
    {
      error() << "unsupported property - only AGp implemented" << eom;
      return 1;
    }

    const exprt &p=property.op0();

    // assumption: time frames 0,...,k-1
    for(unsigned c=0; c<no_timeframes-1; c++)
    {
      exprt tmp(p);
      instantiate(tmp, c, ns);
      solver.set_to_true(tmp);
    }
    
    // claim: time frame k
    {
      exprt tmp(p);
      instantiate(tmp, no_timeframes-1, ns);
      solver.set_to_false(tmp);
    }    
  }

  decision_proceduret::resultt dec_result=
    solver.dec_solve();
  
  switch(dec_result)
  {
  case decision_proceduret::D_SATISFIABLE:
    result("SAT: inductive proof failed, k-induction is inconclusive");
    break;

  case decision_proceduret::D_UNSATISFIABLE:
    result("UNSAT: inductive proof successful, property holds");
    report_success();
    break;

  case decision_proceduret::D_ERROR:
    error() << "Error from decision procedure" << eom;
    return 2;

  default:
    error() << "Unexpected result from decision procedure" << eom;
    return 1;
  }

  return 0;
}
