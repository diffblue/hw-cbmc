/*******************************************************************\

Module: Partial Canonicalization of a Predicate

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#include <verilog/expr2verilog.h>

#include "canonicalize.h"

/*******************************************************************\

Function: canonicalize_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void canonicalize_rec(exprt &expr, bool &negation)
 {
  if(expr.id()=="not")
   {
    if(expr.operands().size()==1)
     {
      exprt tmp;
      tmp.swap(expr.operands()[0]);
      negation=!negation;
      canonicalize_rec(tmp, negation);
      expr.swap(tmp);
     }
   }
  else if(expr.id()=="notequal")
   {
    if(expr.operands().size()==2)
     {
      negation=!negation;
      expr.id("=");
     }
   } 
  else if(expr.id()=="<=" || expr.id()=="<" ||
          expr.id()==">=" || expr.id()==">")
   {
    if(expr.operands().size()==2)
     {
       
     }
   } 
 }

/*******************************************************************\

Function: canonicalize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void canonicalize(exprt &expr, bool &negation)
{
  // we expect an expression of type Boolean
  if(expr.type().id()!="bool")
  {
    std::cerr << expr << "\n";
    std::cerr <<"Debug: expr is \n" << expr2verilog(expr) << "\n";
    std::cerr <<"Debug: type is \n" << expr.type().id_string() << "\n";
	 
    throw "canonicalize expects expression of Boolean type";
  }

  symbol_tablet symbol_table;
  const namespacet ns(symbol_table);
  simplify(expr, ns);

  negation=false;

  canonicalize_rec(expr, negation);
}

/*******************************************************************\

Function: canonicalize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void canonicalize(exprt &expr)
{
  bool negation;

  canonicalize(expr, negation);

  if(negation) expr.make_not();
}

