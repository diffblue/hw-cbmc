/*******************************************************************\

Module: Simulator

Author:  Himanshu Jain
         Daniel Kroening
         Karen Yorav
    
Date: June 2003

Purpose: Simulate an abstract counterexample on the concrete program
to determmine whether it is spurious.

\*******************************************************************/

#ifndef CPROVER_SIMULATOR_H
#define CPROVER_SIMULATOR_H

#include <util/message.h>
#include <util/namespace.h>
#include <util/cmdline.h>

#include <solvers/sat/cnf.h>
#include <solvers/sat/satcheck.h>

#include <trans-netlist/bmc_map.h>
#include <trans-netlist/var_map.h>
#include <trans-netlist/instantiate_netlist.h>
#include <trans-netlist/unwind_netlist.h>

#include "concrete_counterexample.h"
#include "concrete_trans.h"
#include "abstract_trans.h"
#include "predicates.h"
#include "partitioning.h"
#include "abstract_counterexample.h"

class simulatort:public messaget
{
public:
  simulatort(message_handlert &_message_handler,
	     const cmdlinet &_cmdline,
	     const irep_idt &_module_identifier,
	     unsigned _num_threads) :
    messaget(_message_handler),
    cmdline(_cmdline),
    module_identifier(_module_identifier),
    num_threads(_num_threads)
   {

     //One time initializations

     if(!cmdline.isset("gcr"))
       generate_refinement_clusters = 0; //default
     else {
       generate_refinement_clusters = 1;
     }


     if(!cmdline.isset("gcrsize"))
       use_gcr_size = 0; //default, useless if --gcr is not present 
     else 
       {
	 use_gcr_size = 1;
	 max_cluster_size = atoi(cmdline.get_val("gcrsize").c_str());
       }

     if(!cmdline.isset("one_cex_only"))
       remove_one_cex_only = 0; //default
     else 
       remove_one_cex_only = 1;
    
     if(!cmdline.isset("run_till_fix"))
       run_till_fix = 0; //default
     else 
       run_till_fix = 1;
    
     //stats
     num_spurious_steps = 0;
     num_steps_checked = 0;
     num_constraints_found = 0;
     not_spurious_cache_hits = 0;
     
     if(!cmdline.isset("verbose"))
       verbose = false; //default
     else 
       verbose = true;
   }

  const cmdlinet &cmdline;

  bool verbose;

  //Use predicates appearing in the proof of unsatisfiability
  bool generate_refinement_clusters;
  unsigned max_cluster_size ;
  bool use_gcr_size;


  bool remove_one_cex_only;

  bool run_till_fix;

  void out_stats(std::ostream &out);


  bool check_spurious_using_bmc(const symbol_tablet &symbol_table,
				const concrete_transt &concrete_trans,
				const abstract_counterexamplet &abstract_counterexample,
				const exprt property,
				concrete_counterexamplet &concrete_counterexample,
				bool verbose,
				bool simplify);

  bool check_abstract_steps
    (const symbol_tablet &symbol_table,
     const concrete_transt &concrete_trans,
     const abstract_counterexamplet &abstract_counterexample,
     const predicatest &predicates,
     abstract_transition_constrainst &abstract_transition_constrains,
     partitioningt::pred_id_clusterst &refinement_clusters,
     bool verbose,
     bool simplify); 

   void check_spurious_using_simulation_standard
     (const symbol_tablet &symbol_table,
      const concrete_transt &concrete_trans,
      const abstract_counterexamplet &abstract_counterexample,
      const predicatest &predicates,
      std::vector<std::set<unsigned> > &imp_preds_per_state,
      bool add_initial_state,
      bool verbose,
      bool simplify);
  
  void generate_constrains
    (const symbol_tablet &symbol_table,
     const concrete_transt &concrete_trans,
     const predicatest &predicates,
     const spurious_abstract_stepst &spurious_abstract_steps,
     abstract_transition_constrainst &abstract_transition_constrains);
  
  typedef std::map<unsigned, literalt> pred_literal_mappingt;
  typedef std::map<unsigned, int> pred_dimacsint_mappingt;

  //When simulating a counterexample we wan't to remember the mappings of the
  //predicates in each state to the corresponding literals in the SAT instance.
  //Each element in the vector below stores such mapping for some abstract state.
  typedef std::vector<pred_literal_mappingt> vector_pred_literal_mappingt;

  typedef std::vector<pred_dimacsint_mappingt> vector_pred_dimacsint_mappingt;


  bool is_spurious_abstract_transition
    (const symbol_tablet &symbol_table,
     const concrete_transt &concrete_trans,
     const abstract_counterexamplet &abstract_counterexample,
     const predicatest &predicates,
     std::set<unsigned> &imp_init_preds,
     std::set<unsigned> &imp_final_preds,
     bool verbose,
     bool simplify,
     unsigned stepno) ;


   void copy_important_preds(const abstract_statet &abstract_state,
			     const std::set<unsigned> &imp_preds,
			     abstract_constraintt &constraint) const;


  bool check_abstract_steps_standard
    (const symbol_tablet &symbol_table,
     const concrete_transt &concrete_trans,
     const abstract_counterexamplet &abstract_counterexample,
     const predicatest &predicates,
     abstract_transition_constrainst &abstract_transition_constrains,
     partitioningt::pred_id_clusterst &refinement_clusters,
     bool verbose,
     bool simplify) ;
   
protected:
  struct constraintt
   {
    exprt guard, original_guard;
    irept location;
    abstract_counterexamplet::const_iterator abstract_step;
   };

  typedef std::list<constraintt> constraintst;
  
  const irep_idt &module_identifier;

  const unsigned num_threads;

  abstract_transitionst not_spurious_transitions_cache;

  //stats

  unsigned num_spurious_steps;
  unsigned num_steps_checked;
  unsigned num_constraints_found;
  unsigned not_spurious_cache_hits;

   void print_pred_literal_mapping
     (const pred_literal_mappingt &pred_lit_map); 


    void create_cluster
      (const symbol_tablet &symbol_table,
       const std::set<unsigned> init_imp_preds,
       const std::set<unsigned> final_imp_preds,
       const predicatest &predicates,
       predicatest &cluster);

  
  bool add_abstract_state_map_transition(
    const symbol_tablet &symbol_table,
    const abstract_statet &abstract_state,
    const predicatest &predicates,
    const bmc_mapt& map,
    prop_convt &solver,
    bool simplify,
    unsigned start,
    pred_literal_mappingt &pred_literal_mapping) const;
  
  void add_abstract_state_map(
    const symbol_tablet &symbol_table,
    const abstract_statet &abstract_state,
    const predicatest &predicates,
    const bmc_mapt& map,
    propt &solver,
    bool simplify,
    unsigned start,
    pred_literal_mappingt &pred_literal_mapping) ;


  void copy_state(const abstract_statet &abstract_state, 
		  abstract_constraintt &constraint);
  

  void collect_fail_info(const pred_literal_mappingt &pred_literal_map,  
			 satcheck_minisat_coret &satcheck_zcore, 
			 std::set<unsigned> &imp_preds) const;
 
 };

#endif
