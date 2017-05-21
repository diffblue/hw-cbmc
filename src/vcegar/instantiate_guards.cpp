/*******************************************************************\

Module: Used for instantiating guards in the weakest preconditions from
the values obtained from abstract counterexample.

Author: Himanshu Jain, hjain@cs.cmu.edu

\*******************************************************************/

#include <util/simplify_expr.h>
#include <util/namespace.h>

#include <verilog/expr2verilog.h>

#include "instantiate_guards.h"
#include "canonicalize.h"
#include "vcegar_util.h"

/*******************************************************************\

Function: instantiate_predicate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instantiate_predicate(
  const predicatest &predicates,
  const abstract_statet &abstract_state,
  exprt &expr,
  std::set<unsigned> &preds_used_to_simplify)
{
  bool negation;

  canonicalize(expr, negation);

  // see if we have it
  unsigned nr;
  if(predicates.find(expr, nr))
   {
     preds_used_to_simplify.insert(nr);

     if(abstract_state.predicate_values[nr] == 0) {
      expr.make_false();

     }
     else {
      expr.make_true();

     }

     if(negation) {
      expr.make_not();
     }
     else {
     }
  }
}

void instantiate_guards_simplify(
  const predicatest &predicates,
  const abstract_statet &abstract_state,
  exprt &expr,
  std::set<unsigned> &preds_used_to_simplify)
{
  if (expr.type().id() != "bool" && !(expr.has_operands())) 
    return;

  symbol_tablet symbol_table;
  const namespacet ns(symbol_table);
  
  if (expr.has_operands()) {
    if (expr.id()  == "if")
      {
	//instantiate the condition as much as possible
	//not sure if while loop is needed or not

	instantiate_guards_simplify(predicates, abstract_state, expr.op0(), preds_used_to_simplify);
	
	simplify(expr.op0(), ns);
	    

	//pick the appropriate branch depending on the condition
	if (expr.op0().is_true()) 
	  {
	    exprt tmp;
	    tmp.swap(expr.op1());
	    expr.swap(tmp);
	    
	    instantiate_guards_simplify(predicates, abstract_state, expr, preds_used_to_simplify);
	  }
	else if (expr.op0().is_false())
	  {
	    exprt tmp;
	    tmp.swap(expr.op2());
	    expr.swap(tmp);
	    instantiate_guards_simplify(predicates, abstract_state, expr, preds_used_to_simplify);
	  }
	//else we do nothing as the condition is not atomic so no need to instantiate other stuff
      }
    else
      {
	Forall_operands(it, expr)
	  instantiate_guards_simplify(predicates, abstract_state, *it, preds_used_to_simplify);
      }
  }
  
  simplify(expr, ns);
 
  if (!expr.is_constant())
    if (expr.type().id() == "bool")
      instantiate_predicate(predicates, abstract_state, expr, preds_used_to_simplify);
}




