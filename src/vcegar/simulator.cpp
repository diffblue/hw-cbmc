/*******************************************************************\

Module: Simulator

Author: Himanshu Jain

Date: May 2004

Purpose: Simulate an abstract counterexample on the concrete program
to check whether the counterexample is spurious.

\*******************************************************************/

#include <cassert>
#include <iostream>
#include <map>
#include <fstream>
#include <vector>

#include <util/cnf_simplify.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>

#include <solvers/sat/satcheck.h>
#include <solvers/sat/dimacs_cnf.h>

#include <langapi/language_ui.h>

#include <trans-word-level/property_word_level.h>
#include <trans-word-level/instantiate_word_level.h>
#include <trans-netlist/counterexample_netlist.h>

#include "simulator.h"
#include "vcegar_util.h"

/*******************************************************************\

Function: simulatort::print_imp_preds_set

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void print_imp_preds_set(std::set<unsigned> &imp_preds)
{
   for (std::set<unsigned>::const_iterator it = 
	 imp_preds.begin();
       it != imp_preds.end(); it++)
    {
      std::cout <<"b["<<*it<<"] "; 
    }
   std::cout <<"\n";
}


/*******************************************************************\

Function: simulatort::check_spurious_using_bmc

  Inputs:

 Outputs:

 Purpose: check an abstract counterexample
          Only THE LENGTH of the abstract counterexample is used.
          Returns TRUE if the counterexample is spurious,
          and FALSE otherwise

\*******************************************************************/

bool simulatort::check_spurious_using_bmc
 (const symbol_tablet &symbol_table,
  const concrete_transt &concrete_trans,
  const abstract_counterexamplet &abstract_counterexample,
  const exprt spec_property,
  concrete_counterexamplet &concrete_counterexample,
  bool verbose,
  bool simplify) 
{
   
   if (abstract_counterexample.size()>0) {

     std::list<bvt> prop_bv;
     satcheckt satcheck;
     const namespacet ns(symbol_table);
     boolbvt solver(ns, satcheck);

     const transt &trans = concrete_trans.trans_expr;

     int bound = abstract_counterexample.size();

     unwind (trans,
	     *this,
	     solver, 
	     bound, 
	     namespacet(symbol_table),
	     true); //add initial state


     std::list<exprt> properties;

     
     if (!cmdline.isset("claim"))
       {
	 exprt new_property("AG");
	 new_property.copy_to_operands(spec_property);
	 properties.push_back(new_property); 
       }
     else
       {
	 exprt new_property(spec_property);
	 properties.push_back(new_property); 
       }


     property(properties, 
	      prop_bv, 
	      *this,
	      solver, 
	      bound,
	      ns);

     //Run the SAT solver

     if(verbose)
       {
         #ifdef DEBUG
	 std::cout << std::endl;
	 std::cout << "Variables: " << solver->no_literals() << std::endl;
	 std::cout << "Clauses:   " << solver->no_clauses()  << std::endl;
	 std::cout << std::endl;
	 #endif

	 status() << "Running " << satcheck.solver_text() << eom;
       }
     
     switch(satcheck.prop_solve())
       {
       case propt::P_SATISFIABLE:
	 {

	   
	   compute_trans_trace(properties, 
			       prop_bv, 
			       solver, 
			       bound,
			       ns,
			       module_identifier,
			       concrete_counterexample);

	 }
	 break;
       case propt::P_UNSATISFIABLE:
	 return true;
	 break;
       case propt::P_ERROR:
	 std::cout << "Error from SAT solver\n";
	 break;
	 
       default:
	 std::cout << "Unexpected result from SAT solver\n";
       }
      }
   else 
     {
       throw 
	 "Trying to refine, but abstract counterexample has length = 0 !";
     }
   
   return false;
 }



/*******************************************************************\

Function: simulatort::copy_state

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void simulatort::copy_state(
  const abstract_statet &abstract_state, 
  abstract_constraintt &constraint)
{
  std::cout <<"Inside copy_state \n";

  for (std::vector<bool>::const_iterator 
	 p_it = (abstract_state.predicate_values).begin();
       p_it != (abstract_state.predicate_values).end(); p_it++) {
    
    if (*p_it) {
      constraint.push_back(ONE);
    }
    else
      constraint.push_back(ZERO);
  }
}

/*******************************************************************\

Function: simulatort::copy_important_preds

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/
void simulatort::copy_important_preds(const abstract_statet &abstract_state,
				      const std::set<unsigned> &imp_preds,
				      abstract_constraintt &constraint) const
{
  #ifdef DEBUG
  std::cout << abstract_state;
  #endif

  unsigned maxp = max (imp_preds); //find maximum element here

  for (unsigned i = 0; i <= maxp; i++)
    {
      std::set<unsigned>::const_iterator it = imp_preds.find(i);
    
      if (it != imp_preds.end()) {
      
	if (abstract_state.predicate_values[i]) {
	  constraint.push_back(ONE);
	}
	else
	  constraint.push_back(ZERO);
      }
      else {
	constraint.push_back(NON_DET);
      }
    }

  
  #ifdef DEBUG 
  std::cout << "Constrtaint is \n"<< constraint;
  #endif
}




/*******************************************************************\

Function: simulatort::generate_constrains

  Inputs:

 Outputs:

 Purpose: Generate constrains for eliminating spurious counterexamples.

\*******************************************************************/

 void simulatort::generate_constrains
    (const symbol_tablet &symbol_table,
     const concrete_transt &concrete_trans,
     const predicatest &predicates,
     const spurious_abstract_stepst &spurious_abstract_steps,
     abstract_transition_constrainst &abstract_transition_constrains)
{
  for(spurious_abstract_stepst::const_iterator it = spurious_abstract_steps.begin();
      it != spurious_abstract_steps.end(); it++) {
    abstract_constraintt start_state_constrain;
    abstract_constraintt end_state_constrain;

    copy_state(it->first, start_state_constrain);
    copy_state(it->second, end_state_constrain);

    abstract_transition_constrains.insert(std::pair <abstract_constraintt, abstract_constraintt >
					     (start_state_constrain, end_state_constrain));
    
  }
}

/*******************************************************************\

Function: simulatort::create_cluster

  Inputs:

 Outputs:

 Purpose: Given a set of inmporant initial and final predicates, 
it creates a cluster out of them.

\*******************************************************************/

 void simulatort::create_cluster
 (const symbol_tablet &symbol_table,
  const std::set<unsigned> init_imp_preds,
  const std::set<unsigned> final_imp_preds,
  const predicatest &predicates,
  predicatest &cluster)
{
  namespacet ns(symbol_table);

  for(std::set<unsigned>::const_iterator it = init_imp_preds.begin();
      it != init_imp_preds.end(); it++) {
    exprt p(predicates[*it]);
    ns.follow_macros(p);

    cluster.lookup(p, *it, predicatest::INITIAL);
    
  }
  
  
  for(std::set<unsigned>::const_iterator it = final_imp_preds.begin();
      it != final_imp_preds.end(); it++) {
    exprt p(predicates[*it]);
    ns.follow_macros(p);

    rename(p);
    cluster.lookup(p, *it, predicatest::FINAL);
  }
}

/*******************************************************************\

Function: abstractort::out_cache_stats

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void simulatort::out_stats(std::ostream &out)
{
  status() << "#Not spurious cache hits " << not_spurious_cache_hits
           << " simulated " << num_steps_checked
           << ", spurious " << num_spurious_steps
           << ", new constraints " << num_constraints_found
           << eom;
}

/*******************************************************************\

Function: simulatort::collect_fail_info

  Inputs:

 Outputs:

 Purpose: reason of unsatisfiability

\*******************************************************************/

void simulatort::collect_fail_info(
  const pred_literal_mappingt &pred_literal_map,  
  satcheck_minisat_coret &satcheck_core, 
  std::set<unsigned> &imp_preds) const
{
  for(pred_literal_mappingt::const_iterator it=
      pred_literal_map.begin();
      it != pred_literal_map.end();
      it++)
  {
      if (satcheck_core.is_in_core(it->second))
	{
	  imp_preds.insert(it->first);
	}
  }
}

/*******************************************************************\

Function: simulatort::add_abstract_state_map

  Inputs:

 Outputs:

 Purpose: Maintain the mapping from a predicate to literalt

\*******************************************************************/

void simulatort::add_abstract_state_map(
  const symbol_tablet &symbol_table,
  const abstract_statet &abstract_state,
  const predicatest &predicates,
  const bmc_mapt& map,
  propt &solver,
  bool simplify,
  unsigned start,
  pred_literal_mappingt &pred_literal_mapping) 
{  
  namespacet ns(symbol_table);

  unsigned pred_num = 0;
  for (std::vector<bool>::const_iterator 
	 p_it = (abstract_state.predicate_values).begin();
       p_it != (abstract_state.predicate_values).end(); p_it++) 
    {
      exprt predicate(predicates[pred_num]);
      
      literalt pl = instantiate_convert(
					solver,
					map,
					predicate,
					start, start+1,
					ns,
					*this); // message

      bool pl_val = *p_it;
      assert(!pl.is_constant() || (pl.is_true() && pl_val) || 
	     (pl.is_false() && !pl_val));

      if (!pl.is_constant())
	{
	  solver.l_set_to(pl, pl_val);

	  assert(pl.var_no() <= solver.no_variables());
      
	  assert ( pl.dimacs() != 0);
	  pred_literal_mapping.insert(std::pair<unsigned, literalt>
				      (pred_num, pl)); 
	}
      
      pred_num++;
    }
}



/*******************************************************************\

Function: simulatort::add_abstract_state_map

  Inputs:

 Outputs:

 Purpose: Maintain the mapping from a predicate to literalt

\*******************************************************************/

bool simulatort::add_abstract_state_map_transition(
  const symbol_tablet &symbol_table,
  const abstract_statet &abstract_state,
  const predicatest &predicates,
  const bmc_mapt& map,
  prop_convt &solver,
  bool simplify,
  unsigned start,
  pred_literal_mappingt &pred_literal_mapping) const
{  
  namespacet ns(symbol_table);

  unsigned pred_num = 0;
  for (std::vector<bool>::const_iterator 
	 p_it = (abstract_state.predicate_values).begin();
       p_it != (abstract_state.predicate_values).end(); p_it++) 
    {
      exprt predicate(predicates[pred_num]);
      
      instantiate(predicate, start, ns);
      literalt pl=solver.convert(predicate);


      bool pl_val = *p_it;
      
      if (pl.is_true() && !pl_val) 
	{
	  //we do not care about the literal assigned to pred_num 
	  pred_literal_mapping.clear();
	  pred_literal_mapping.insert(std::pair<unsigned, literalt>
				      (pred_num, pl));
	  return false;
	}
      
      if (pl.is_false() && pl_val) 
	{
	  pred_literal_mapping.clear();
	  pred_literal_mapping.insert(std::pair<unsigned, literalt>
				      (pred_num, pl));
	  return false;
	}
      
      
      assert(!pl.is_constant() || (pl.is_true() && pl_val) || 
	     (pl.is_false() && !pl_val));
      
      if(!pl.is_constant())
	{
	  assert(pl.var_no() <= solver.prop.no_variables());
	  assert ( pl.dimacs() != 0);
	  solver.prop.l_set_to(pl, pl_val);
	  pred_literal_mapping.insert(std::pair<unsigned, literalt>
				      (pred_num, pl)); 
	}
      
      pred_num++;
    }
  return true;
}

/*******************************************************************\

Function: simulatort::is_spurious_abstract_transition

  Inputs:

 Outputs:

 Purpose: Generating CNF using dimacs so that ..proofs of 
unsatisfiability can be extracted by using chaff externally.

\*******************************************************************/

bool simulatort::is_spurious_abstract_transition(
  const symbol_tablet &symbol_table,
  const concrete_transt &concrete_trans,
  const abstract_counterexamplet &abstract_counterexample,
  const predicatest &predicates,
  std::set<unsigned> &imp_init_preds,
  std::set<unsigned> &imp_final_preds,
  bool verbose,
  bool simplify,
  unsigned stepno) 
{
  assert(stepno < abstract_counterexample.size()-1);
  namespacet ns(symbol_table);
  const transt &trans = concrete_trans.trans_expr;

  satcheck_minisat_coret satcheck;
  bmc_mapt map;

  map.var_map = concrete_trans.var_map;
  map.map_timeframes(satcheck, 2);

  boolbvt boolbv(satcheck);
  boolbv.set_message_handler(get_message_handler());


  exprt instantiated_trans(trans.trans());
  instantiate(instantiated_trans, 0, ns);

  exprt instantiated_invar0(trans.invar());
  instantiate(instantiated_invar0, 0, ns);
  
  exprt instantiated_invar1(trans.invar());
  instantiate(instantiated_invar1, 1, ns);
  
  boolbv.set_to_true(instantiated_invar0);
  boolbv.set_to_true(instantiated_invar1);
  boolbv.set_to_true(instantiated_trans);


  pred_literal_mappingt initial_pred_literal_map, 
    final_pred_literal_map;

  // Add the start abstract state
  bool b1= add_abstract_state_map_transition
    (symbol_table, 
     abstract_counterexample[stepno],
     predicates,
     map, boolbv, simplify, 0, 
     initial_pred_literal_map);

  if (!b1)
    {
      assert(initial_pred_literal_map.size() == 1);
      imp_init_preds.insert(initial_pred_literal_map.begin()->first);
      return true;
    }

  // Add the end abstract state
  bool b2 = add_abstract_state_map_transition
    (symbol_table, 
     abstract_counterexample[stepno+1],
     predicates,
     map, boolbv, simplify, 1,  
     final_pred_literal_map);

  if (!b2)
    {
      assert(final_pred_literal_map.size() == 1);
      imp_final_preds.insert(final_pred_literal_map.begin()->first);
      return true;
    }

  
  if (verbose)
    status() << "Running " << satcheck.solver_text() << eom;

  switch(satcheck.prop_solve())
    {
    case propt::P_SATISFIABLE:
      return false; //can be simulated
      break;  
      
    case propt::P_UNSATISFIABLE: 
      {
	collect_fail_info(initial_pred_literal_map,  
			  satcheck,
			  imp_init_preds);
	
	collect_fail_info(final_pred_literal_map,  
			  satcheck,
			  imp_final_preds);

        #ifdef DEBUG
	std::cout <<"Important initial set of predicates \n";
	print_imp_preds_set(imp_init_preds);

	std::cout <<"Important final set of predicates \n";
	print_imp_preds_set(imp_final_preds);
        #endif
      }
      break;
      
    case propt::P_ERROR:
      throw "Warning! Error from SAT solver when simulating abstract abstract transition \n";
      break;
      
    default:
      throw "Unexpected result from SAT solver\n";
      break;
    }
  return true; //transition is spurious
} 


bool simulatort::check_abstract_steps_standard
(const symbol_tablet &symbol_table,
 const concrete_transt &concrete_trans,
 const abstract_counterexamplet &abstract_counterexample,
 const predicatest &predicates,
 abstract_transition_constrainst &abstract_transition_constrains,
 partitioningt::pred_id_clusterst &refinement_clusters,
 bool verbose,
 bool simplify) 
{
  bool     result = false;
  unsigned num_new_clusters = 0;

  for (unsigned i=0; i<abstract_counterexample.size()-1; i++) 
  {
    const abstract_statet &start = abstract_counterexample[i];
    const abstract_statet &end   = abstract_counterexample[i+1];

    if (not_spurious_transitions_cache.find(abstract_transitiont(start,end)) != 
	not_spurious_transitions_cache.end())
      {
	not_spurious_cache_hits++;
	continue;
      }

    std::set<unsigned> imp_init_preds, imp_final_preds;

    #ifdef DEBUG
    std::cout <<"Abstract transition ["<<i <<"]->["<<i+1<<"] \n";
    #endif

    num_steps_checked++;


    bool status =  is_spurious_abstract_transition(
      symbol_table,
      concrete_trans,
      abstract_counterexample,
      predicates,
      imp_init_preds,
      imp_final_preds,
      verbose,
      simplify,
      i) ;

    if(status) 
    {
      #ifdef DEBUG
      std::cout <<" is spurious\n";
      #endif
      result = true;
      
      num_spurious_steps++;
      
      abstract_constraintt start_state_constrain;
      abstract_constraintt end_state_constrain;
      
      
      copy_important_preds(abstract_counterexample[i], 
                           imp_init_preds,
                           start_state_constrain);
      copy_important_preds(abstract_counterexample[i+1],
                           imp_final_preds,
                           end_state_constrain);
      
      if (generate_refinement_clusters ) 
      {
        //Also create a new cluster of important final and initial predicates. This
        //will hopefully be small and will make the abstraction less coarse.
        
        if (!use_gcr_size || (imp_init_preds.size() + imp_final_preds.size() <= max_cluster_size ))
        {
          refinement_clusters.insert(std::pair<std::set<unsigned>, std::set<unsigned> >
                                     (imp_init_preds, imp_final_preds));
          
          num_new_clusters++;
        }
      }
     
      unsigned old_size = abstract_transition_constrains.size();
      abstract_transition_constrains.insert(
        std::pair <abstract_constraintt, abstract_constraintt >
        (start_state_constrain, end_state_constrain));

      unsigned new_size = abstract_transition_constrains.size(); 
      
      if (new_size > old_size)
        num_constraints_found++;
    }
    else 
    {
      #ifdef DEBUG
      std::cout <<"NOT spurious\n";
      #endif

      //      std::cout << "Adding to cache "<<start<< "->"<<end<<"\n";

      std::pair<abstract_transitionst::iterator, bool> at_b = 
	not_spurious_transitions_cache.insert(abstract_transitiont(start,end));
	
      assert (at_b.second);
    }
  }

  return result; 
}

/*******************************************************************\

Function: simulatort::check_spurious_using_simulation_standard

  Inputs:

 Outputs:

 Purpose: Does BMC but also takes the predicate values into account.
          The aim is to make use of unsat cores and identify predicates
          whose weakest pre-condition needs to be taken.  
 
          Use standard interface for zcore.  
\*******************************************************************/

void simulatort::check_spurious_using_simulation_standard(
  const symbol_tablet &symbol_table,
  const concrete_transt &concrete_trans,
  const abstract_counterexamplet &abstract_counterexample,
  const predicatest &predicates,
  std::vector<std::set<unsigned> > &imp_preds_per_state,
  bool add_initial_state,
  bool verbose,
  bool simplify) 
{
  assert(!abstract_counterexample.empty());
  assert(add_initial_state);

  satcheck_minisat_coret satcheck;
  bmc_mapt map;
  namespacet ns(symbol_table);
 
  map.var_map = concrete_trans.var_map;

  map.map_timeframes(satcheck, abstract_counterexample.size());


  const transt &trans = concrete_trans.trans_expr;
  
  boolbvt boolbv(satcheck);
  boolbv.set_message_handler(get_message_handler());


  //add initial state constrains depending on add_initial_state
    unwind(trans,
	   *this,
	   satcheck, 
	   map, 
	   symbol_table); 


  //now start adding abstract states
  vector_pred_literal_mappingt mappings;

  for (unsigned i = 0; i < abstract_counterexample.size() ; i++) 
  {
    pred_literal_mappingt mapping_i;
 
    #ifdef DEBUG 
    std::cout <<"Adding abstract state ["<< i <<"] \n";
    std::cout << abstract_counterexample[i];
    #endif

    add_abstract_state_map(symbol_table, 
                           abstract_counterexample[i],
                           predicates,
                           map, satcheck, simplify, i, 
                           mapping_i);
    
    mappings.push_back(mapping_i);
  }

  switch(satcheck.prop_solve())
  {
  case propt::P_UNSATISFIABLE:
    break;
    
  default:
    throw "satcheck_zcore returned error";
  }
  
  //Now collect fail info
  
  for (unsigned i = 0; i < abstract_counterexample.size() ; i++) 
  {
    std::set<unsigned> imp_preds_in_state_i;
    
    collect_fail_info(mappings[i],  
                      satcheck,
                      imp_preds_in_state_i);
    
    #ifdef DEBUG
    std::cout << "Important predicates in state "<<i<<"\n";
    print_imp_preds_set(imp_preds_in_state_i);
    #endif

    imp_preds_per_state.push_back(imp_preds_in_state_i);
  }
}


