/*******************************************************************\

Module: Model Checker Base Class

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_MODELCHECKER_H
#define CPROVER_MODELCHECKER_H

#include <message.h>

#include "abstract_counterexample.h"

/* A general purpose model checker */
class modelcheckert:public messaget
 {
 public:
  modelcheckert(message_handlert &_message_handler):
    messaget(_message_handler)
    {
    }

  // A return value of TRUE means the program is correct,
  // if FALSE is returned, counterexample will contain the counterexample
   virtual bool check
     (const abstract_transt &abstract_trans, 
      const abstract_transition_constrainst &abstract_transition_constrains,
      const weakest_precondition_constrainst &weakest_precondition_constrains,
      const abstract_initial_constrainst &abstract_initial_constrains,
      abstract_counterexamplet &abstract_counterexample)=0;
 };

#endif



