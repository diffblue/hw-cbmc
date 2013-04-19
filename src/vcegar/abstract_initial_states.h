/*******************************************************************\

Module: Predicate Abstraction of a Predicate

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CEGAR_ABSTRACT_PREDICATE_H
#define CEGAR_ABSTRACT_PREDICATE_H

#include <set>
#include <satqe/cubes.h>

class abstract_initial_statest
 {
 public:
  cubest cubes;
  std::vector<unsigned> input_predicates;
  
  void clear()
   {
    cubes.clear();
    input_predicates.clear();
   }
 };

#endif
