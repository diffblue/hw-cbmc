/*******************************************************************\

Module: SMV Model Checker Interface

Author: Daniel Kroening
        Himanshu Jain
  
  Date: June 2003

\*******************************************************************/

#ifndef CPROVER_MODELCHECKER_SMV_H
#define CPROVER_MODELCHECKER_SMV_H

#include <iosfwd>

#include "modelchecker.h"

class modelchecker_smvt:public modelcheckert
 {
 public:
  typedef enum { CMU_SMV, NUSMV, CADENCE_SMV } enginet;
 
  modelchecker_smvt(message_handlert &_message_handler,
		    enginet _engine, bool v, bool claims_option, bool _absref3):
    modelcheckert(_message_handler),
    engine(_engine),
    verbose(v),
    claim(claims_option),
    absref3(_absref3)
    {
      switch(engine)
	{
	case CMU_SMV:     status() << "Using the modelchecker: CMU_SMV" << eom; 
	  break;
	case NUSMV:       status() << "Using the modelchecker: NUSMV" << eom; 
	  break;
	case CADENCE_SMV: status() << "Using the modelchecker: CADENCE_SMV" << eom;
	  break;
	default:
	  throw "Unknown modelchecker  \n";
	}
      
      if (absref3)
	status() << "Absref3 set to true for Cadence SMV" << eom;
    }

  // A return value of TRUE means the program is correct,
  // if FALSE is returned, counterexample will contain the counterexample
  virtual bool check
   (const abstract_transt &abstract_trans,
    const abstract_transition_constrainst &abstract_transition_constrains,
    const weakest_precondition_constrainst &weakest_precondition_constrains,
    const abstract_initial_constrainst &abstract_initial_constrains,
    abstract_counterexamplet &abstract_counterexample);

 private:
  enginet engine;

  std::vector<std::string> variable_names;

  bool verbose; 
  bool claim;
  bool absref3;

  void print_constrain
    (const abstract_constraintt &start,
     const abstract_constraintt &final,
     std::ostream &out) ; 

  void add_weakest_precondition_constrain
    (const abstract_constraintt &start1,
     const abstract_constraintt &final1,
     const abstract_constraintt &start2,
     const abstract_constraintt &final2,
     std::ostream &out);
 
 
  void build_smv_file
   (const abstract_transt &abstract_trans,
    const abstract_transition_constrainst &abstract_transition_constrains,
    const weakest_precondition_constrainst &weakest_precondition_constrains,
    const abstract_initial_constrainst &abstract_initial_constrains,
    std::ostream &out);


  void build_smv_file
    (const abstract_transt &abstract_trans,  
     const abstract_transition_constrainst &abstract_transition_constrains,
     const weakest_precondition_constrainst &weakest_precondition_constrains,
     const abstract_initial_constrainst &abstract_initial_constrains,
     bool threaded,
     std::ostream &out);
    
  void build_smv_file_global_variables
   (const abstract_transt &abstract_trans,
    std::ostream &out);

  void build_smv_file_trans_cluster
    (const abstract_transt &abstract_trans,
     const abstract_transition_relationt &cluster_trans,
     unsigned clsuter_no,
     bool threaded,
     std::ostream &out);

  void build_smv_file_spec
   (const abstract_transt &abstract_trans,
    bool threaded,
    std::ostream &out);
    
  void build_smv_file_init_cluster
    (const abstract_transt &abstract_trans,
     const abstract_initial_statest &initial_states,
     unsigned cluster_no,
     std::ostream &out);

  void remove_spurious_transition
    (const abstract_constraintt &start,
     const abstract_constraintt &final,
     std::ostream &out);
    
  bool read_result
   (std::istream &out1,
    std::istream &out2,
    std::istream &out_ce, //result from cadence smv
    const abstract_transt &abstract_trans,
    abstract_counterexamplet &counterexample);

  void read_counterexample
   (const std::list<std::string> &file,
    std::list<std::string>::const_iterator it,
    const abstract_transt &abstract_trans,
    abstract_counterexamplet &counterexample);

  class smv_ce_thread_infot
  {
  public:
    std::vector<bool> guards;
    unsigned PC;
    bool runs;
  };

  typedef std::vector<smv_ce_thread_infot> thread_infost;
    
  void read_counterexample_store
   (abstract_counterexamplet &counterexample,
    thread_infost &thread_infos,
    abstract_statet abstract_state);
    
   void instantiate_expression(exprt &expr); 
    
   
  
  bool is_variable_name(const std::string &variable_name);
  void get_variable_names(const abstract_transt &abstract_trans);
  
  typedef std::map<exprt, std::string> nondet_symbolst;
  nondet_symbolst nondet_symbols;


  void read_counterexample_loop_cadence_smv
    (const std::list<std::string> &file,
     std::list<std::string>::const_iterator it,
     const abstract_transt &abstract_trans,
     abstract_counterexamplet &counterexample);
  
  
  void read_counterexample_cadence_smv
    (const std::list<std::string> &file,
     std::list<std::string>::const_iterator it,
     const abstract_transt &abstract_trans,
     abstract_counterexamplet &counterexample);
  
  bool read_result_cadence_smv
    (std::istream &out_ce,
     const abstract_transt &abstract_trans,
     abstract_counterexamplet &counterexample);

  void remove_spurious_initial_state
    (const abstract_constraintt &start,
     std::ostream &out);
  
 }; 

#endif
