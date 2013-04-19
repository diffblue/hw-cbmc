/*******************************************************************\

Module: Predicate Discovery

Author:  Himanshu Jain, hjain@cs.cmu.edu

\*******************************************************************/

#include <assert.h>

#include "discover_predicates.h"
#include "canonicalize.h"
#include "vcegar_util.h"
#include <simplify_expr.h>




void discover_simple_preds_simplified(const exprt &expr,
                             std::set<predicatet> &predicates,
                             bool canonicalized, bool &isAtomic)
 {
   if (expr.type().id() != "bool" && !(expr.has_operands())) {
     return;
   }

   if (expr.has_operands()) {
      std::set<predicatet> new_predicates;

      if (expr.id() == "if")
	{
	  discover_simple_preds_simplified(expr.op0(), new_predicates, canonicalized, isAtomic);
	  assert (!new_predicates.empty());
	}
      else
	{
	  forall_operands(it, expr)
	    {
	      discover_simple_preds_simplified(*it, new_predicates, canonicalized, isAtomic);
	    }
	}

      if (new_predicates.size() > 0) {
	//move the predicates from new_predicates to the predicates
	for (std::set<exprt>::const_iterator it = new_predicates.begin();
	     it != new_predicates.end(); it++ ) 
	  {
	    exprt pred (*it);
	    predicates.insert(pred);
	  }
	
	new_predicates.clear();
	
	isAtomic = false;
	
	return;
      }
   }
   else if(expr.id()=="constant")
     {
       return;
     }

   if (expr.type().id() == "bool") {

    if(!canonicalized)
      {
	exprt tmp(expr);
	bool negation;
	canonicalize(tmp, negation);
	discover_simple_preds_simplified(tmp, predicates, true, isAtomic);
      }
    else {
      #if 1
      exprt tmp_expr(expr);
      simplify(tmp_expr);

      if (!(tmp_expr.is_true() || tmp_expr.is_false()) && containsSymbol(tmp_expr))
	{
	  isAtomic = true;
	  predicates.insert(tmp_expr);
	}
      #else
      isAtomic = true;
      predicates.insert(expr);
      #endif
    }
   }
 }




/*******************************************************************\

Function: collect_case_assignments

  Inputs:

 Outputs:

 Purpose: For an expr of form say (a==1)?b:(a==2)?c+d:c-d, we obtain
the assignment set as {b, c+d, c-d}.

\*******************************************************************/

void collect_case_assignments(const exprt &expr, std::set<exprt> &assignments, 
			      unsigned select)
{
  if (select == 1) {
    if (expr.id()=="typecast") {
      if ((expr.operands()[0]).id() == "if")
	return collect_case_assignments(expr.operands()[0], assignments, 2);
      else
	assert(0);
    }
  }

  if (expr.id() == "if") {
    collect_case_assignments((expr.operands())[1], assignments, 2);
    collect_case_assignments((expr.operands())[2], assignments, 2);
    return;
  }

  exprt new_assign(expr);
  assignments.insert(expr);
}

/*******************************************************************\

Function: involves_case

  Inputs:

 Outputs:

 Purpose: Predicates of the  {if ()..... } == 2 ; case statement is 
made up of nested if's.

\*******************************************************************/

bool involves_case(const exprt &expr)
{
  if (expr.id() == "if") {
     return true;
  }
  
  if (expr.id() == "typecast") {
    if (((expr.operands())[0]).id() == "if")
      return true;
  }
  return false;
}


/*******************************************************************\

Function: gen_lhs_eq_rhs_preds

  Inputs:

 Outputs:

 Purpose: For two sets of the form {x,y, x+y} and {x, f, a+b}
 generates a set of predicates as {x==x, y==x, x+y==x, ....}
Cartesian product basically!! 
\*******************************************************************/

void gen_lhs_eq_rhs_preds(const std::set<exprt> &lhs_assignment, 
			  const std::set<exprt> &rhs_assignment,  
			  std::set<predicatet> &predicates)
{
  for (std::set<exprt>::const_iterator it1 = lhs_assignment.begin();
       it1 != lhs_assignment.end(); it1++){
    for (std::set<exprt>::const_iterator it2 = rhs_assignment.begin();
       it2 != rhs_assignment.end(); it2++){
      
      if (it1->is_constant() && it2->is_constant())
	break;

       exprt new_variable_expr(*it1);
       exprt new_definition_expr(*it2);
       
       exprt new_predicate("=", typet("bool"));
       new_predicate.copy_to_operands(new_variable_expr);
       new_predicate.copy_to_operands(new_definition_expr);
       predicates.insert(new_predicate);
       
    }
    
  }
}


/*******************************************************************\

Function: discover_case_assign_predicates

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void discover_case_assign_predicates(const exprt &expr,
				     std::set<predicatet> &predicates,
				     bool canonicalized)
{
   if (expr.type().id() != "bool" && !(expr.has_operands())) {
     return;
   }

  if(expr.id()=="and" || expr.id()=="=>" ||
     expr.id()=="not" || expr.id()=="or" || expr.id()=="if" || 
     expr.id()=="typecast" || 
     expr.id()=="extractbit" ||
     expr.id()=="reduction_or" ||
     expr.id()=="reduction_and" ||
     expr.id()=="reduction_nor" ||
     expr.id()=="reduction_nand" ||
     expr.id()=="reduction_xor" ||
     expr.id()=="reduction_xnor" 
     || expr.id()=="AG"
     )
    {
    forall_operands(it, expr)
      discover_case_assign_predicates(*it, predicates, canonicalized);

    return;
   }
  else if(expr.id()=="=" || expr.id()=="notequal")
   {
     if(expr.operands().size()==2)
       {
	 bool complex1=false, complex2=false;

	 if(expr.operands()[0].type().id()=="bool" &&
	    expr.operands()[1].type().id()=="bool")
	   {
	     discover_case_assign_predicates(expr.operands()[0], predicates, canonicalized);
	     discover_case_assign_predicates(expr.operands()[1], predicates, canonicalized);
	     return;
	   }

	 if ((expr.operands()[0]).has_operands()){
	   complex1 = involves_case(expr.operands()[0]);
	   discover_case_assign_predicates(expr.operands()[0], predicates, canonicalized);
	 }

	 if ((expr.operands()[1]).has_operands()){
	   complex2 = involves_case(expr.operands()[1]);
	   discover_case_assign_predicates(expr.operands()[1], predicates, canonicalized);
	 }

	 std::set<exprt> lhs_assignments;
	 std::set<exprt> rhs_assignments;
	 
	 if (complex1 || complex2){
	   if (complex1) 
	     collect_case_assignments(expr.operands()[0], lhs_assignments, 1);
	   else
	     lhs_assignments.insert(expr.operands()[0]);
	   
	   if (complex2) 
	     collect_case_assignments(expr.operands()[1], rhs_assignments, 1);
	   else
	     rhs_assignments.insert(expr.operands()[1]);

	   gen_lhs_eq_rhs_preds(lhs_assignments, rhs_assignments, predicates);

	   return;
	 }
       }
   }
  else if(expr.id()=="constant")
    {
    // we don't care about Boolean constants
      return;
    }


  
  if (expr.type().id() == "bool") {
    if(!canonicalized)
      {
	exprt tmp(expr);
	bool negation;
	canonicalize(tmp, negation);
	discover_case_assign_predicates(tmp, predicates, true);
      }
    else {
      predicates.insert(expr);
    }
  }
}





/*******************************************************************\

Function: discover_predicates

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void discover_predicates(const exprt &expr,
                         std::set<predicatet> &predicates,
			 int choice, bool &isAtomic)
 {
   if (choice == 1) {
     throw "Support for discover=1 removed \n";
   }
   else if (choice == 2) {
     throw "Support for discover=2 removed \n";
   }
   else if (choice == 3) {
     discover_case_assign_predicates(expr, predicates, false);
   }
   else if (choice == 4) {
     #if 0
     discover_simple_preds_simplified(expr, predicates, false, isAtomic);
     #else
     if (containsSymbol(expr))
       discover_simple_preds_simplified(expr, predicates, false, isAtomic);
     else
       isAtomic = false; //some constant predicate
     #endif
   }
 }
