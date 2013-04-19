/*******************************************************************\

Module: Refiner

Author: Himanshu Jain, Daniel Kroening

Date: June 2004

Purpose: Calculate predicates for predicate abstraction.

\*******************************************************************/

#ifndef CPROVER_REFINER_H
#define CPROVER_REFINER_H

#include <cassert>

#include <util/message.h>
#include <util/symbol_table.h>
#include <util/cmdline.h>

#include "concrete_trans.h"
#include "predicates.h"
#include "abstract_counterexample.h"
#include "network_info.h"

class refinert:public messaget
 {
 public:
  refinert(message_handlert &_message_handler, 
	   const cmdlinet &_cmdline) :
    messaget(_message_handler),
    cmdline(_cmdline)
   {
     if(!cmdline.isset("discover")) {
       discover = 4; //default old was 2
       #ifdef DEBUG
       std::cout << "Discovering preds in weakest pre-conditions with "<<discover<<"\n";
       #endif
     }
     else 
       discover=atoi(cmdline.getval("discover"));
     
     #ifdef DEBUG
     std::cout <<"discover is: "<<discover<<"\n";
     #endif

     if(!cmdline.isset("nowpcons")) 
       {
	 add_wp_cons = true;
	 #ifdef DEBUG
	 std::cout << "Adding weakest pre-condition constraints \n";
	 #endif
       }
     else 
       {
	 add_wp_cons = false;
	 std::cout << "Not adding weakest pre-condition constraints \n";
       }
     
     if (cmdline.isset("verbose"))
       verbose=true;
     else
       verbose=false;
     
   }
  
  bool verbose;
  const cmdlinet &cmdline;
  int discover;
  bool add_wp_cons;


  // Calculates the initial set of predicates for the given program
  void init_preds(predicatest &predicates, 
		  const concrete_transt &concrete_trans, 
		  const contextt &context); // context is for DEBUG

  // Calculates the initial set of predicates for the given program
  void init_preds(predicatest &predicates, 
                  const std::vector<exprt> &initial_predicates);


 void spurious_ce(predicatest &predicates,
		  const concrete_transt &concrete_trans,
		  const abstract_counterexamplet &spurious_counterexample,
		  const contextt &context,
		  const exprt property,
		  const network_infot &network,
		  std::vector<std::set<unsigned> > &imp_preds_per_state,
		  weakest_precondition_constrainst &weakest_precondition_constrains,
		  bool generate_extra_preds); 

 void generate_predicates
   (predicatest &predicates, 
    const abstract_counterexamplet &spurious_counterexample,
    const contextt &context, 
    const network_infot &network,
    std::vector<std::set<unsigned> > &imp_preds_per_state,
    weakest_precondition_constrainst &weakest_precondition_constrains,
    bool generate_extra_preds);

 void compute_wp_seed_predicate
   (predicatest &predicates, 
    const abstract_counterexamplet &spurious_counterexample,
    const contextt &context, 
    const network_infot &network,
    weakest_precondition_constrainst &weakest_precondition_constrains, //constraints relating a predicate and its wp
    unsigned pred_num, //we will take wp of this
    int len, //no. of steps for which to take the weakest pre-condition
    std::vector<std::set<unsigned> > &imp_preds_per_state,
    bool generate_extra_preds
    );

 void relate_pred_and_wp
   (const abstract_statet &abstract_state,
    const std::set<unsigned> preds_used_to_simplify,
    weakest_precondition_constrainst &weakest_precondition_constrains,
    unsigned pred_num, 
    unsigned wp_pred_num);   
 };

#endif
