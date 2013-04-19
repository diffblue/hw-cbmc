/*******************************************************************\

Module: Predicate Manager

Author: Daniel Kroening, kroening@kroening.com
        Himanshu Jain, hjain@cs.cmu.edu

\*******************************************************************/

#include <cassert>

#include <verilog/expr2verilog.h>

#include "predicates.h"

/*******************************************************************\

Function: predicatest::lookup

  Inputs:

 Outputs:

 Purpose: find (and add, if not found) a predicate

\*******************************************************************/

unsigned predicatest::lookup(const predicatet &predicate)
 {
    std::pair<predicate_mapt::iterator, bool> result=
      predicate_map.insert(
      std::pair<predicatet, unsigned>
      (predicate, predicate_vector.size()));

   if(result.second) // already there?
    {
     // actually inserted
     predicate_vector.push_back(result.first);
    }

   predicate_state.insert(std::pair<predicatet, statet>
			  (predicate, NOT_DEFINED));
   

   return result.first->second;
 }


/*******************************************************************\

Function: predicatest::lookup

  Inputs:

 Outputs:

 Purpose: find (and add, if not found) a predicate

\*******************************************************************/

void predicatest::lookup(const predicatet &predicate, 
			 unsigned predicate_num, 
			 statet state)
 {
    std::pair<predicate_mapt::iterator, bool> result=
      predicate_map.insert(
      std::pair<predicatet, unsigned>
      (predicate, predicate_num));


   if(result.second) // already there?
    {
     // actually inserted
     predicate_vector.push_back(result.first);
    }

   
   predicate_state.insert(std::pair<predicatet, statet>
			  (predicate, state));

 }


/*******************************************************************\

Function: operator<<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream& operator<< (std::ostream& out,
                          const predicatest &predicates)
 {
   for(unsigned i=0; i<predicates.size(); i++)
    {
     std::string code;

     unsigned nr;
     if (!predicates.find(predicates[i], nr)) 
       nr = i;

     out << "b" << nr << " <=> " << expr2verilog(predicates[i]) << std::endl;
    }

  return out;
 }

/*******************************************************************\

Function: operator<<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


void predicatest::get_pred_ids(std::pair<std::set<unsigned>, std::set<unsigned> >
			       &pred_id_set_pair) const
{
  for(unsigned i=0; i < size(); i++) 
    {                                     
      predicatest::statet state;
      unsigned nr;
      
      this->get_info(predicate_vector[i]->first, nr, state);
      
      switch(state) {
      case predicatest::INITIAL: {
	pred_id_set_pair.first.insert(nr);
	break;
      }
      case predicatest::FINAL: {
	pred_id_set_pair.second.insert(nr);
	break;
      }
      case predicatest::NOT_DEFINED: {
	assert(0);
	break;
      }
      }
    }
  
  return;
}


/*******************************************************************\

Function: operator<<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream& operator<< (std::ostream& out,
                          const std::set<predicatet> &ps)
{
  for(std::set<predicatet>::const_iterator psit = ps.begin(); psit != ps.end(); psit++)
    {
      out << expr2verilog(*psit)<< "\n";
    }
  return out;
}
