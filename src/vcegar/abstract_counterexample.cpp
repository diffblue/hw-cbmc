/*******************************************************************\

Module: Counterexamples

Author: Daniel Kroening

  Date: June 2003

\*******************************************************************/

#include <langapi/mode.h>
#include <langapi/languages.h>

#include "abstract_counterexample.h"

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &operator<<
 (std::ostream &out, const abstract_statet &state)
{
  for(unsigned i=0; i<state.predicate_values.size(); i++)
    out << " b" << i << "=" << state.predicate_values[i] <<" ";
  
  out << std::endl;
  
  return out;
}

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &operator<< 
(std::ostream &out, const abstract_counterexamplet &cex)
{
  unsigned i = 0;
  
  for (abstract_counterexamplet::const_iterator accit  = cex.begin();
       accit != cex.end(); accit++)
  {
    out << "State: " <<i<<"\n";
    out << *accit; 
    i++;
  }

  out << std::endl;

  return out;
}

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &operator<<
 (std::ostream &out, const abstract_constraintt &constraint)
{
  for(unsigned i=0; i<constraint.size(); i++)
    {
      
      switch (constraint[i]) { 
      case ZERO :
	out << " b" << i << "=" << 0 <<" ";
	break;
      case ONE:
	out << " b" << i << "=" << 1 <<" ";
	break;
      case NON_DET:
	out << " b" << i << "= *"   <<" ";
	break;
      }
    }
    
  out << std::endl;

  return out;
}

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream& operator<< (
  std::ostream& out,
  const abstract_transition_constraintt &abstract_transition_constraint)
{
  out << abstract_transition_constraint.first;
  out << "--------> \n";
  out << abstract_transition_constraint.second;

  return out;
}
