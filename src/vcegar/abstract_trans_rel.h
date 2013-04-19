/*******************************************************************\

Module: Predicate Abstraction of circuits

Author: Daniel Kroening, kroening@kroening.com
         
\*******************************************************************/

#ifndef CEGAR_ABSTRACT_TRANS_REL_H
#define CEGAR_ABSTRACT_TRANS_REL_H

#include <set>
#include <satqe/cubes.h>


class abstract_transition_relationt
 {
 public:
  cubest cubes;
  std::vector<unsigned> input_predicates;
  std::vector<unsigned> output_predicates;
  std::vector<unsigned> unchanged_predicates;
  
  void clear()
   {
    cubes.clear();
    input_predicates.clear();
    output_predicates.clear();
    unchanged_predicates.clear();
   }
 };


#endif
