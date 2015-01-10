/*******************************************************************\

Module: Counterexamples

Author: Daniel Kroening
        Karen Yorav 
        Himanshu Jain
   
Date: June 2003

\*******************************************************************/

#ifndef CPROVER_ABSTRACT_COUNTEREXAMPLE_H
#define CPROVER_ABSTRACT_COUNTEREXAMPLE_H

#include <iosfwd>
#include <vector>
#include <list>

#include "abstract_trans.h"

/* An abstract state */
class abstract_statet
{
public:
  typedef std::vector<bool> predicate_valuest;
  predicate_valuest predicate_values;

  friend std::ostream& operator<<
    (std::ostream& out,
     const abstract_statet &state);
  
  friend bool operator<(const abstract_statet &as1, const abstract_statet &as2)
  {
    return (as1.predicate_values < as2.predicate_values);
  }
};

/* An abstract conterexample */

typedef std::vector<abstract_statet> abstract_counterexamplet;
typedef std::vector<std::pair<abstract_statet, abstract_statet> > 
				 spurious_abstract_stepst;

typedef std::pair<abstract_statet, abstract_statet> abstract_transitiont;
typedef std::set<abstract_transitiont> abstract_transitionst;

typedef enum {ZERO, ONE, NON_DET} valuet;

//Exactly similar to spurious abstract state. Only that it contains
//vector of boolean values, whereas here we also have a NON_DET value possible 
//in valuet.
typedef std::vector<valuet> abstract_constraintt;

typedef std::pair<abstract_constraintt,  abstract_constraintt> abstract_transition_constraintt;

typedef std::set<abstract_transition_constraintt> abstract_transition_constrainst;

typedef std::set<std::pair<abstract_transition_constraintt, abstract_transition_constraintt > > weakest_precondition_constrainst;

typedef std::set<abstract_constraintt> abstract_initial_constrainst;

std::ostream& operator<<
     (std::ostream& out,
      const abstract_constraintt &state);

std::ostream& operator<<
     (std::ostream& out,
      const abstract_transition_constraintt &abstract_transition_constraint);

std::ostream &operator<< 
(std::ostream &out, const abstract_counterexamplet &cex);
                          
#endif
