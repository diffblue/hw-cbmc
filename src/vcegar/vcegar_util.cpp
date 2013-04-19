/*******************************************************************\

Module: Utilities for VCEGAR

Author: Himanshu Jain

Date: April 2004

\*******************************************************************/

#include <cassert>
#include <map>
#include <vector>

#include <util/i2string.h>
#include <util/namespace.h>

#include <verilog/expr2verilog.h>

#include "vcegar_util.h"
#include "canonicalize.h"

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

std::ostream& operator<< (std::ostream& out,
			  const std::set<unsigned> &uiset) 
{

  for(std::set<unsigned>::const_iterator it= uiset.begin(); it != uiset.end(); it++) {
    out <<*it<<" ";
  }
  out <<"\n";

  return out;
}

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

std::ostream& operator<< (std::ostream& out,
			  const literalt &lit)
{
  out <<lit.sign()<<"["<<lit.var_no()<<"] \n";
  return out;
}

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose: return the maximum element of a set containing unsigned.

\*******************************************************************/

unsigned max (const std::set<unsigned> &uiset)
{
  unsigned max = 0;

  for(std::set<unsigned>::const_iterator it= uiset.begin(); it != uiset.end(); it++) {
    if (*it > max)
      max = *it;
  }

  return max;
}


/*******************************************************************\

Function: rename

  Inputs:

 Outputs:

 Purpose: Renames a current state predicate to a next state predicate

\*******************************************************************/

void rename(exprt &expr)
 {
   if(expr.has_operands())
     Forall_operands(it, expr)
       rename(*it);
   
   if(expr.id()=="symbol")
     {
       expr.id("next_symbol");
     }
 }


/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void containsSymbolRecur (const exprt &expr, bool &result)
{
  if(expr.has_operands())
    forall_operands(it, expr)
      containsSymbolRecur(*it, result);
  
  if(expr.id()=="symbol")
    {
      result = true;
    }
}


/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose: Returns true if the given expr contains some variable
          i.e., a register, input etc. Otherwise, returns false.
          For example, it should return false for weird predicate
         line 0[1].
\*******************************************************************/

bool containsSymbol (const exprt &expr)
{
  bool result  = false;

  containsSymbolRecur (expr, result);
  
  return result;
}



/*******************************************************************\

Function: get_next_state_function

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void get_next_state_function
(std::string name, //Should be a latch
 const exprt &trans_rel, //op[2] will be just fine. 
 exprt& definition)
{  
  if (!trans_rel.has_operands()) return;


  if (trans_rel.id()=="if") { 
    return; //we don't expect to obtain definitions inside if statements
  }

  if(trans_rel.id()=="=")
    {
      exprt t1= (trans_rel.operands())[0];
      exprt t2= (trans_rel.operands())[1];
      
      if (t1.id()== "next_symbol") {
	if (t1.find("identifier").id() == name) {
	  exprt prop(t2); 
	  definition = prop;
	  //definition = t2;
	  return;
	}   
      }
    }
  
  if(trans_rel.has_operands())
    forall_operands(it, trans_rel)
      get_next_state_function(name, *it, definition);
}



/*******************************************************************\

Function: find_symbols

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void find_symbols(
  const exprt &predicate, 
  std::set<irep_idt> &symbols, 
  const irep_idt name)
{
  if(predicate.has_operands())
    forall_operands(it, predicate)
      find_symbols(*it, symbols, name);
  
  if(predicate.id()==name)
    symbols.insert(predicate.get(ID_identifier));
}

/*******************************************************************\

Function: 

Inputs: subset (A, B)

Outputs:

Purpose: returns true if A is a subset of B,  false otherwise.

\*******************************************************************/

bool subset(
  const std::set<irep_idt> &set1,
  const std::set<irep_idt> &set2) 
{
  for(std::set<irep_idt>::const_iterator it1= set1.begin();
       it1 != set1.end(); it1++)
  {
    std::set<irep_idt>::const_iterator it2 = set2.find(*it1);
    if (it2 == set2.end())
      return false;
  }
  return true;
}


/*******************************************************************\

Function: get_type_integer

 Inputs:

 Outputs:

 Purpose: Old vcegar code assumed that get_type returns an integer
          but this is no longer the case. So this routine uses
          get_type to get an enum and then converts it to integer.

          just casting enum returned by get_type to integer wont' be
          good  as the order to WIRE and MACRO in vartypet has changed.
\*******************************************************************/

int get_type_integer(const var_mapt &vmap, const irep_idt &s)
{
  switch(vmap.get_type(s))
  {
  case var_mapt::vart::VAR_LATCH: return 1;
  case var_mapt::vart::VAR_INPUT: return 2; 
  case var_mapt::vart::VAR_WIRE:  return 3;
  default: return -1;
  }
}

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

std::ostream& operator<< (std::ostream& out,
			  const std::vector<std::set<unsigned> > &vec_vec_unsigned)
{
  int count = 0;
  for (std::vector<std::set<unsigned> >::const_iterator 
	 it =  vec_vec_unsigned.begin(); 
       it != vec_vec_unsigned.end(); it++)
    {
      out << "State "<<count <<":";
      out <<*it ;
      count++;
    }

  return out;
}


/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

std::string double2string(const double& x)
{
  std::ostringstream o;
  if (!(o << x)) 
    throw "ERROR: when converting double to string";
  return o.str();
}
