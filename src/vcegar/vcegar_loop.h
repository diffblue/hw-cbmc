/*******************************************************************\

Module: VCEGAR Loop

Author: Himanshu Jain, Daniel Kroening


Date: June 2003

\*******************************************************************/

#ifndef CPROVER_VCEGAR_LOOP_H
#define CPROVER_VCEGAR_LOOP_H

#include <set>

#include <util/message.h>
#include <util/expr_util.h>
#include <util/time_stopping.h>

#include <langapi/language_ui.h>

#include "concrete_trans.h" 
#include "modelchecker.h" 
#include "simulator.h" 
#include "abstractor.h" 
#include "refiner.h" 
#include "specification.h"
#include "network_info.h"

/* This class implements the VCEGAR loop, given the proper tools */

class vcegar_loopt: public messaget
 {
 public:
  vcegar_loopt(
    concrete_transt &_concrete_trans, 
    const specificationt &_spec,
    const symbol_tablet &_symbol_table,
    abstractort &_abstractor,
    refinert &_refiner,
    modelcheckert &_modelchecker,
    simulatort &_simulator,
    message_handlert &_message_handler,
    unsigned _max_iterations,
    const cmdlinet &_cmdline,
    const std::vector<exprt> &_user_provided_preds,
    ui_message_handlert::uit _ui):
    messaget(_message_handler),
    concrete_trans(_concrete_trans),
    spec(_spec),
    symbol_table(_symbol_table),
    abstractor(_abstractor),
    refiner(_refiner),
    modelchecker(_modelchecker),
    simulator(_simulator),
    max_iterations(_max_iterations),
    cmdline(_cmdline),
    user_provided_preds(_user_provided_preds),
    ui(_ui)
   {
     
     if(!cmdline.isset("noconstrain"))
       constrain = 1; //default
     else
       constrain = 0;
     
     if(!cmdline.isset("refine1"))
       {
	 refine1 = 0; //default
       }
     else
       {
	 refine1 = 1;
	 constrain = 0;
       }

     if(!cmdline.isset("gcr"))
       {
	 generate_clusters = 0; //default
       }
     else
       {
	 generate_clusters = 1;
       }
     
     if(cmdline.isset("siege"))
       use_siege = 1; 
     else
       use_siege = 0; //default

     if(cmdline.isset("i"))
       unbounded_cegar_iterations = false; 
     else
       unbounded_cegar_iterations = true; //default
     
     if (cmdline.isset("verbose"))
       verbose = true;
     else
       verbose = false;



     iteration_spurious_transition=0;
     iteration_weakest_precondition=0;
     iteration_weakest_precondition_extra=0;
   }

  void go();

 private:  
  void obtain_abstract_property();
  void print_stats(unsigned iterations,
		   const fine_timet&, 
		   const fine_timet&, 
		   const fine_timet&, 
		   const fine_timet&);

  void additional_stats(const fine_timet &spurious_trans_time,
			const fine_timet &bmc_time,
			const fine_timet &unsat_time,
			const fine_timet &wp_time); 
    

  void copy_clusters(const partitioningt::predicate_clusterst 
				   &refine_clusters); 
  
  void run_experimental_code();

  void print_mapping();

  void report_success();
  void report_failure();

  void add_initial_state_constrain(const abstract_counterexamplet &spurious_counterexample,
				   const std::vector<std::set<unsigned> > &imp_preds_per_state,
				   abstract_initial_constrainst &abstract_initial_constrains);

  concrete_transt &concrete_trans;
  const specificationt &spec;
  const symbol_tablet &symbol_table;
  abstractort &abstractor;
  refinert &refiner;
  modelcheckert &modelchecker;
  simulatort &simulator;

  //clusters (of predicate id) obtained by refinement
  partitioningt::pred_id_clusterst pred_id_clusters;

  abstract_transition_constrainst  abstract_transition_constrains; 
  weakest_precondition_constrainst weakest_precondition_constrains; 
  abstract_initial_constrainst     abstract_initial_constrains;

  unsigned max_iterations;
  predicatest predicates;  
  const cmdlinet &cmdline;
  bool constrain;
  bool refine1; //use unsat core to check spurious transitions or take weakest pre-conditions
  bool create_abstraction;
  std::vector<exprt> user_provided_preds;
  bool generate_clusters; //generate clusters from refinement 
  bool use_siege; //use siege SAT solver
  bool unbounded_cegar_iterations;
  bool verbose;
  ui_message_handlert::uit ui;

  unsigned iteration_spurious_transition;
  unsigned iteration_weakest_precondition;
  unsigned iteration_weakest_precondition_extra;  
 };

#endif




