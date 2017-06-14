/*******************************************************************\

Module: Abstractor (generates abstract program given a set of predicates)

Author: Himanshu Jain

Date: April 2004

\*******************************************************************/

#include <map>
#include <vector>

#include <util/namespace.h>
#include <util/find_symbols.h>

#include <verilog/expr2verilog.h>
#include <solvers/flattening/boolbv.h>
#include <satqe/satqe_satcheck.h>
#include <trans-word-level/instantiate_word_level.h>
#include <trans-netlist/unwind_netlist.h>

#include "abstractor.h"
#include "predabs_aux.h"
#include "partitioning.h"

/*******************************************************************\

Function: abstractort::abstract_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void abstractort::abstract_variables(
  const predicatest &predicates,
  abstract_transt::variablest &variables)
{
  variables.clear();
  variables.resize(predicates.size());

  for(unsigned i=0; i<predicates.size(); i++) 
    variables[i].description=expr2verilog(predicates[i]);
}

/*******************************************************************\

Function: abstractort::calc_abstraction

  Inputs:

 Outputs:

 Purpose: compute abstraction according to set of predicates

\*******************************************************************/

void abstractort::calc_abstraction(
  const predicatest &predicates, 
  const concrete_transt &concrete_trans,
  const namespacet &ns,
  const network_infot &network,
  const partitioningt::pred_id_clusterst &pred_id_clusters)
{
  abstract_variables(predicates, abstract_trans.variables);

  calc_abstraction_with_partition(
    predicates, concrete_trans, 
    ns, network, pred_id_clusters);
}


/*******************************************************************\

Function: abstractort::calc_abstraction_with_partition

  Inputs:

 Outputs:

 Purpose: compute abstraction according to set of predicates which 
          will be partitioned for scalibility

\*******************************************************************/

void abstractort::calc_abstraction_with_partition(
  const predicatest &predicates, 
  const concrete_transt &concrete_trans,
  const namespacet &ns,
  const network_infot &network,
  const partitioningt::pred_id_clusterst &pred_id_clusters)
{
  // copy trans
  transt trans(concrete_trans.trans_expr);
   
  ns.follow_macros(trans); 

  if(abs_init_states)
  {
    calc_init_states_abstraction(
      predicates, 
      concrete_trans,
      trans,
      ns,
      network);
  }

  calc_trans_rel_abstraction(
    predicates, 
    concrete_trans,
    trans,
    ns,
    network);

  // Using the clusters generated from the removal
  // of spurious abstract counterexamples
   
  if(use_refinement_clusters) 
  {
    refinement_guided_partitioning_abstraction(
      predicates, 
      concrete_trans,
      trans,
      ns,
      network,
      pred_id_clusters);
  }
}

/*******************************************************************\

Function: abstractort::calc_init_states_abstraction

  Inputs:

 Outputs:

 Purpose: Calculates initial states in the abstraction.

\*******************************************************************/

void abstractort::calc_init_states_abstraction(
  const predicatest &predicates, 
  const concrete_transt &concrete_trans,
  const transt &trans,
  const namespacet &ns,
  const network_infot &network)
{
  partitioningt partition;
    
  init_pred_clusters.clear();
   
  #ifdef DEBUG
  std::cout << "Partitioning predicates for initial set of predicates";
  #endif

  partition.partition_initial_predicates(
    predicates, 
    ns,
    trans,
    concrete_trans.var_map,
    network,
    init_pred_clusters);
  
  #ifdef DEBUG
  std::cout << "..done\n";
  #endif

  unsigned i=0;

  //Remove the old init state clusters
  abstract_trans.abstract_init_vector.clear();
   
  for(partitioningt::predicate_clusterst::const_iterator
      it=init_pred_clusters.begin();
      it!=init_pred_clusters.end();
      it++) 
  {
       #ifdef DEBUG
       std::cout <<"Initial states cluster no. "<<i <<" \n";
       std::cout << *it;
       #endif

       abstract_trans.abstract_init_vector.
	 push_back(abstract_initial_statest());
       
       unsigned insert_at = abstract_trans.abstract_init_vector.size()-1;
       bool cache_hit = false;
       
       partitioningt::pred_id_set_pairt init_id_set;

       if (init_state_caching)
	 {
	   it->get_pred_ids(init_id_set);
	   
	   states_cubes_cachet::const_iterator init_it =  init_cubes_cache.find(init_id_set);
	   
	   init_cache_num_access++;
	   
	   if (init_it != init_cubes_cache.end())
	     {
	       abstract_trans.abstract_init_vector[insert_at] = init_it -> second;
	       cache_hit = true;
	       init_cache_num_hits ++ ;
	     }
	 }
       
       if (!init_state_caching || !cache_hit)
	 {
    	   calc_abstract_initial_states(
    	     *it, 
	     concrete_trans,
	     trans, //follow macros is assumed to be done
	     abstract_trans.abstract_init_vector[insert_at],
	     ns);
	   
	   if (init_state_caching)
	     {
	       init_cubes_cache.insert(std::pair <partitioningt::pred_id_set_pairt, 
				       abstract_initial_statest>
				       (init_id_set, abstract_trans.abstract_init_vector[insert_at]));
	       
	     }

	   i++;
	 }
       
       if (it->size() > max_init_state_cluster_size)
	 max_init_state_cluster_size = it->size();
  }

  num_init_clusters = abstract_trans.abstract_init_vector.size();
   
}

/*******************************************************************\

Function: abstractort::calc_trans_rel_abstraction

  Inputs:

 Outputs:

 Purpose: Calculates transition relation of the abstraction.

\*******************************************************************/

void abstractort::calc_trans_rel_abstraction(
  const predicatest &predicates, 
  const concrete_transt &concrete_trans,
  const transt &trans,
  const namespacet &ns,
  const network_infot &network)
{
  partitioningt partition;
    
  pred_clusters.clear();
   
  if(verbose)
    status() << "Computing partitioned transition relation of the abstraction" << eom;
   
  partition.partition_predicates(
    predicates, 
    trans, 
    ns,
    concrete_trans.var_map,
    network,
    pred_clusters,
    partitioning_strategy,
    verbose);
   
  unsigned i=0;
   
  //Remove the old clusters
  abstract_trans.abstract_trans_vector.clear();
   
  for(partitioningt::predicate_clusterst::const_iterator
      it=pred_clusters.begin();
      it!=pred_clusters.end();
      it++)
  {
    if(verbose)
    {
      std::cout <<"Transition relation cluster no. "<<i <<" \n";
      std::cout << *it;
    }

    abstract_trans.abstract_trans_vector.
      push_back(abstract_transition_relationt());

    bool cache_hit = false;
       
    partitioningt::pred_id_set_pairt trans_id_set;

    if(trans_rel_caching)
    {
      it->get_pred_ids(trans_id_set);
	 
      trans_cubes_cachet::const_iterator trans_it =  
        trans_cubes_cache.find(trans_id_set);
	 
      trans_cache_num_access++;
	 
      if (trans_it != trans_cubes_cache.end())
      {
        abstract_trans.abstract_trans_vector.back() = trans_it -> second;
        cache_hit = true;
        trans_cache_num_hits ++ ;
      }
    }
       
    if(!trans_rel_caching || !cache_hit)
    {
      calc_abstract_trans_rel(
        *it, 
	concrete_trans,
	trans, //follow macros is assumed to be done
	abstract_trans.abstract_trans_vector.back(),
	ns);
	 
      trans_cubes_cache.insert(
        std::pair <partitioningt::pred_id_set_pairt, 
		   abstract_transition_relationt>
	  (trans_id_set, abstract_trans.abstract_trans_vector.back()));
      i++;
    }
     
    if(it->size() > max_trans_cluster_size)
      max_trans_cluster_size = it->size();
  }
   
  num_trans_clusters = abstract_trans.abstract_trans_vector.size();
}

/*******************************************************************\

Function: abstractort::refinement_guided_partitioning_abstraction

  Inputs:

 Outputs:

 Purpose: Calculates transition relation of clusters generated from 
refinement.

\*******************************************************************/

void abstractort::refinement_guided_partitioning_abstraction(
  const predicatest &predicates, 
  const concrete_transt &concrete_trans,
  const transt &trans,
  const namespacet &ns,
  const network_infot &network,
  const partitioningt::pred_id_clusterst &pred_id_clusters)
{
   partitioningt partition;

   abstract_trans.refinement_preds_trans_vector.clear();
   
   #ifdef DEBUG
   std::cout <<"Refinement generated clusters \n";
   partition.print_clusters (pred_id_clusters);
   #endif
       
   for (partitioningt::pred_id_clusterst::const_iterator it = pred_id_clusters.begin();
	it != pred_id_clusters.end(); it++)
     {
       abstract_trans.refinement_preds_trans_vector.
	 push_back(abstract_transition_relationt());
       
       unsigned insert_at = abstract_trans.refinement_preds_trans_vector.size()-1;
       bool cache_hit = false;
       
       if (pred_id_clusters_caching)
	 {
	   trans_cubes_cachet::const_iterator pcit =  refine_cubes_cache.find(*it);
	
	   pred_id_cache_num_access++;

	   if (pcit != refine_cubes_cache.end())
	     {
	       abstract_trans.refinement_preds_trans_vector[insert_at] = pcit -> second;
	       cache_hit = true;
	       pred_id_cache_num_hits ++ ;
	     }
	 }
       
       #ifdef DEBUG
       std::cout <<"Refine clusters cache: "<<pred_id_cache_num_hits<<"\n";
       #endif

       if (!pred_id_clusters_caching || !cache_hit)
	 {
	   //compute actual predicates from the pred id set
	   predicatest pred_cluster; 
	   
	   partition.obtain_refinement_cluster
	     (predicates,
	      network,
	      ns,
	      *it,
	      pred_cluster);
	   
	   calc_abstract_trans_rel
	     (pred_cluster, 
	      concrete_trans,
	      trans, //follow macros is assumed to be done
	      abstract_trans.refinement_preds_trans_vector[insert_at],
	      ns);
	   
	   if (pred_id_clusters_caching) 
	     {
	       refine_cubes_cache.insert(std::pair <partitioningt::pred_id_set_pairt, 
					 abstract_transition_relationt>
					 (*it, 
					  abstract_trans.refinement_preds_trans_vector[insert_at]));
	     }
	   
	   if (pred_cluster.size() > max_trans_cluster_size)
	     max_trans_cluster_size = pred_cluster.size();
	 }
     }

}



/*******************************************************************\

Function: abstractort::calc_abstract_trans_rel

  Inputs:

 Outputs:

 Purpose: compute abstract transition relation according to the
          given set of predicates.
          Predicates contains a mixture of current state and next
          state predicates.  

\*******************************************************************/

void abstractort::calc_abstract_trans_rel(
  const predicatest &cluster, 
  const concrete_transt &concrete_trans,
  const transt &trans, //follow macros is assumed to be done
  abstract_transition_relationt &abstract_transition_relation,
  const namespacet &ns)
{
  //It is assumed that follow macros has already been called for
  // the concrete transition relation and predicates in the "cluster".

  //Obtain the initial and final set of predicates
  std::vector<exprt> initial_predicates, final_predicates;
  std::vector<unsigned> input, output;

  for(unsigned i=0; i<cluster.size(); i++) //No test is made to test if the value
  {                                        //of a predicate does not change.    
    predicatest::statet state;

    unsigned nr;
    cluster.get_info(cluster[i], nr, state);

    switch(state)
    {
    case predicatest::INITIAL:
      {
        input.push_back(nr);
        initial_predicates.push_back(cluster[i]);
        break;
      }

    case predicatest::FINAL:
      {
        output.push_back(nr);
        final_predicates.push_back(cluster[i]);

        break;
      }
    case predicatest::NOT_DEFINED:
      {
	assert(false);
	break;
      }
    }
  }

  #ifdef DEBUG
  std::cout <<" ASSERTITION REMOVED FOR GCR\n";
  #endif
  //   assert(output.size()!=0);
    
  // Now obtain the cubes for the abstract transition relation.
  // We will create a new SAT solver object.

  satqe_satcheckt satqe_satcheck;
  satqe_satcheck.set_message_handler(get_message_handler());
   
  boolbvt boolbv(ns, satqe_satcheck);
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

  cube_sett trans_cube_set;
  satqe_satcheck.set_cube_set(trans_cube_set);
    
  std::vector<unsigned> important_variables;
  important_variables.reserve(input.size() + output.size());
    
  if(show_cubes) 
    std::cout << " Order of cubes:";

  for(unsigned i=0; i<input.size(); i++)
  {
    unsigned p=input[i];
    exprt tmp(initial_predicates[i]);
    instantiate(tmp, 0, ns);
    
    literalt l=make_pos(boolbv, tmp);
    important_variables.push_back(l.var_no());
    abstract_transition_relation.input_predicates.push_back(p);
       
    if(show_cubes)
      std::cout << " " << p;
  }
   
  if(show_cubes)
    std::cout <<" |";
   
  for(unsigned i=0; i<output.size(); i++)
  {
    unsigned p=output[i];
    exprt tmp(final_predicates[i]);
    instantiate(tmp, 0, ns);
    literalt l=make_pos(boolbv, tmp);
    important_variables.push_back(l.var_no());
    abstract_transition_relation.output_predicates.push_back(p);

    if(show_cubes)
      std::cout << " " << p;
  }

  if(show_cubes)
    std::cout << std::endl;

  // set important variables
  satqe_satcheck.set_important_variables(important_variables);

  // solve it
  switch(boolbv.dec_solve())
  {
  case decision_proceduret::D_UNSATISFIABLE:
    // OK, this is what we expect
    break;

  default:
    throw "unexpected result from predabs_sat1.solve()";
  }

  debug() <<"Generated "
          << i2string(trans_cube_set.no_insertions()) << " cube(s)"
          << eom;

  if(show_cubes)
    std::cout << trans_cube_set;

  abstract_transition_relation.cubes.swap(trans_cube_set);
}

/*******************************************************************\

Function: abstractort::calc_abstract_initial_states

  Inputs:

 Outputs:

 Purpose: computes set of abstract initial states according to the given set of predicates.
          Predicates contains only current state predicates.  

\*******************************************************************/

void abstractort::calc_abstract_initial_states(
  const predicatest &cluster, 
  const concrete_transt &concrete_trans,
  const transt &trans, //follow macros is assumed to be done
  abstract_initial_statest 
  &abstract_initial_states,
  const namespacet &ns)
{
  //It is assumed that follow macros has already been called for
  // the concrete transition relation and predicates in the "cluster".

  //Obtain the initial set of predicates
  std::vector<exprt> initial_predicates;
  std::vector<unsigned> input;

  for(unsigned i=0; i<cluster.size(); i++) //No test is made to test if the value
  {                                        //of a predicate does not change.    
    predicatest::statet state;
    unsigned nr;
    cluster.get_info(cluster[i], nr, state);

    switch(state)
    {
    case predicatest::INITIAL:
      {
        input.push_back(nr);
        exprt input(cluster[i]); 
	initial_predicates.push_back(input);
	
	break;
      }

    case predicatest::FINAL:
      {
	assert(0);
	break;
      }

    case predicatest::NOT_DEFINED:
      {
	assert(0);
	break;
      }
    }
  }

  assert(input.size()!=0);
    
  // Now obtain the cubes for the abstract transition relation.
  // We will create a new SAT solver object.
  
  satqe_satcheckt satqe_satcheck;
  boolbvt boolbv(ns, satqe_satcheck);

  boolbv.set_message_handler(get_message_handler());
  satqe_satcheck.set_message_handler(get_message_handler());

  cube_sett initial;
  satqe_satcheck.set_cube_set(initial);


  exprt instantiated_invar(trans.invar());
  instantiate(instantiated_invar, 0, ns);

  exprt instantiated_init(trans.init());
  instantiate(instantiated_init, 0, ns);

  boolbv.set_to_true(instantiated_invar);  
  boolbv.set_to_true(instantiated_init);


  std::vector<unsigned> important_variables;
  important_variables.reserve(input.size());

  for(unsigned i=0; i<input.size(); i++)
  {
    unsigned p=input[i];
    exprt tmp(initial_predicates[i]);
    instantiate(tmp, 0, ns);
    literalt l=make_pos(boolbv, tmp);
    important_variables.push_back(l.var_no());
    abstract_initial_states.input_predicates.push_back(p);
  }

  // set important variables
  satqe_satcheck.set_important_variables(important_variables);

  // solve it
  switch(boolbv.dec_solve())
  {
  case decision_proceduret::D_UNSATISFIABLE:
    // OK, this is what we expect
    break;

  default:
    throw "unexpected result from predabs_sat1.solve()";
  }

  // std::cout<<" The abstract transition relation \n";
  debug() << "Generated " <<
          << i2string(initial.no_insertions()) <, " cube(s)\n"
          << eom;

  if(show_cubes)
    std::cout << initial;

  //store the cubes
  abstract_initial_states.cubes.swap(initial);
}

/*******************************************************************\

Function: abstractort::out_cache_stats

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void abstractort::out_stats(std::ostream &out)
{
  status() << "#Cache sizes: " << trans_cubes_cache.size() << ","
           << refine_cubes_cache.size() << ","
           << init_cubes_cache.size();
  status() << "#[hits/access] Trans cache:[" << trans_cache_num_hits
           << "/" << trans_cache_num_access << "], "
           << "Refine cache:[" << pred_id_cache_num_hits << "/"
           << pred_id_cache_num_access << "], "
           << "Init cache:[" << init_cache_num_hits << "/"
           << init_cache_num_access << "]";
}

