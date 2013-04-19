/*******************************************************************\

Module: An Abstract Transition System

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_ABSTRACT_TRANS_H
#define CPROVER_ABSTRACT_TRANS_H

#include "abstract_trans_rel.h"
#include "abstract_initial_states.h"
#include "specification.h"

class abstract_transt
{
public:
  //Vector of transition relation constrains
  std::vector<abstract_transition_relationt> abstract_trans_vector;
  std::vector<abstract_initial_statest> abstract_init_vector;
     
  std::vector<abstract_transition_relationt> refinement_preds_trans_vector;

  // variables
  struct variablet
  {
    std::string description;
  };

  typedef std::vector<variablet> variablest;
  variablest variables;

  specificationt abstract_spec;
};

#endif
