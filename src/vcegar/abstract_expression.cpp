/*******************************************************************\

Module: Create abstract expression from concrete one

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include "abstract_expression.h"
#include "canonicalize.h"

/*******************************************************************\

Function: make_it_a_predicate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void make_it_a_predicate(const predicatest &predicates,
                         exprt &expr)
 {
  bool negation;

  canonicalize(expr, negation);

  // see if we have it
  unsigned nr;
  if(predicates.find(expr, nr))
   {
    // yes, we do!

    // see if it is a constant
    if(predicates[nr].is_true())
      expr.make_true();
    else if(predicates[nr].is_false())
      expr.make_false();
    else
     {
      expr=exprt("predicate_symbol", typet("bool"));
      expr.set("identifier", nr);
     }

    if(negation)
      expr.make_not();
   }
  else
   {
    // nah, we don't
    // make it nondeterministic choice
    exprt tmp("nondet_symbol", typet("bool"));
    tmp.add("expression").swap(expr);
    expr.swap(tmp);
   }
 }

/*******************************************************************\

Function: abstract_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void abstract_expression(const predicatest &predicates,
                         exprt &expr)
 {
  if(expr.type().id()!="bool")
    {
      std::cout << expr << "\n";
      throw "abstract_expression expects expression of type Boolean";
    }

  if(expr.id()=="and" || expr.id()=="or" ||
     expr.id()=="not" || expr.id()=="=>" ||
     expr.id()=="xor" ||
     expr.id()=="AG" 
     )
   {
    Forall_operands(it, expr)
      abstract_expression(predicates, *it);
   }
  else if(expr.id()=="=" || expr.id()=="notequal")
   {
    if(expr.operands().size()!=2)
      throw expr.id_string()+" takes two operands";

    // Is it equality on Booleans?

    if(expr.operands()[0].type().id()=="bool" &&
       expr.operands()[1].type().id()=="bool")
     {
      // leave it in

      Forall_operands(it, expr)
        abstract_expression(predicates, *it);
     }
    else // other types, make it a predicate
      make_it_a_predicate(predicates, expr);
   }
  else if(expr.is_constant())
   {
    // leave it as is
   }
  else
    make_it_a_predicate(predicates, expr);
 }

/*******************************************************************\

Function: abstract_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void abstract_expression(const predicatest &predicates,
                         exprt &expr, int choice)
 {
   switch(choice) {
   case 1:{ 
     abstract_expression(predicates,expr); 
     break;
   }
   case 2: {
     //property is itself a predicate
     make_it_a_predicate(predicates, expr); 
     break;
   }
   }
   
 }
