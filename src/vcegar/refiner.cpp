/*******************************************************************\
  
Module: Refinement for VCEGAR. Finds new word level predicates. And
        constraints for syntactic abstraction.

Author: Himanshu Jain, Daniel Kroening 

Date: Nov 2004
 
\*******************************************************************/

#include <cassert>
#include <iostream>

#include <util/namespace.h>
#include <util/cnf_simplify.h>
#include <util/simplify_expr.h>

#include <verilog/expr2verilog.h>

#include "refiner.h"
#include "discover_predicates.h"
#include "canonicalize.h"
#include "partitioning.h"
#include "vcegar_util.h"
#include "instantiate_guards.h"

//#define DEBUG

/*******************************************************************\

Function: refinert::init_preds

  Inputs:

 Outputs:

 Purpose: generate initial set of predicates for a concrete program

\*******************************************************************/

void refinert::init_preds(predicatest &predicates, 
			  const concrete_transt &concrete_trans, 
			  const symbol_tablet &symbol_table // only for DEBUG
			  )
{
  status() << "Calculating initial set of predicates" << eom;
}

/*******************************************************************\

Function: refinert::init_preds

  Inputs:

 Outputs:

 Purpose: generate initial set of predicates for a concrete program

\*******************************************************************/

void refinert::init_preds(predicatest &predicates, 
			  const std::vector<exprt> &initial_predicates)
{
  #ifdef DEBUG
  status() << "Using provided set of initial predicates" << eom;
  #endif

  for(std::vector<predicatet>::const_iterator
      p_it=initial_predicates.begin();
      p_it!=initial_predicates.end();
      p_it++)
  {
    bool negation;
    exprt p(*p_it);
    canonicalize(p, negation);
    predicates.lookup(p);
  }

}

/*******************************************************************\

Function: refinert::relate_pred_and_wp

  Inputs:

 Outputs:

 Purpose: Update weakest_precondition_constrains, by entering the 
relationship between a predicate and its weakest pre-condition.

Some valuation of consitions => p_j == wp (p_i, transition relation)


Basically, we will add (trans1 | trans2) to the abstraction.

\*******************************************************************/


void refinert::relate_pred_and_wp
(const abstract_statet &abstract_state,
 const std::set<unsigned> preds_used_to_simplify,
 weakest_precondition_constrainst &weakest_precondition_constrains,
 unsigned pred_num, unsigned wp_pred_num
 )
{
  abstract_transition_constraintt trans1;
  abstract_transition_constraintt trans2;

  //determine maximum pred_num occuring in preds_used_to_simplify
  unsigned maxp_simplify = max(preds_used_to_simplify);

  unsigned total_num_preds = 
    (maxp_simplify > wp_pred_num)?
    ((maxp_simplify > pred_num)?maxp_simplify:pred_num):
    ((wp_pred_num > pred_num)?wp_pred_num:pred_num);

  #ifdef DEBUG
  std::cout <<"maxp_simplify, pred_num, wp_pred_num are"<<maxp_simplify
	    <<" "<<pred_num<<" "<<wp_pred_num<<"\n";
  #endif

  // initialize

  for (unsigned i = 0; i <= total_num_preds; i++) {
    trans1.first.push_back(NON_DET); //initial state
    trans1.second.push_back(NON_DET); //final state
    trans2.first.push_back(NON_DET); //initial state
    trans2.second.push_back(NON_DET); //final state
  }

  //now set the valuation for predicate used when simplifying monolithic weakest pre-condition

  for (std::set<unsigned>::const_iterator it = preds_used_to_simplify.begin();
       it != preds_used_to_simplify.end(); it++) 
    {

      if (abstract_state.predicate_values[*it] == 0) {
	trans1.first[*it] = ZERO;
	trans2.first[*it] = ZERO;
      }
      else {
	assert (abstract_state.predicate_values[*it] == 1);
	trans1.first[*it] = ONE;
	trans2.first[*it] = ONE;
      }
    }


  // now it pred no. i is wp of pred. no j, then make preds i and j ZERO in trans1
  // and make preds i and j ONE in trans2 (since pred no. i == next (j))
  assert(trans1.second[pred_num] == NON_DET);
  assert(trans2.second[pred_num] == NON_DET);

  trans1.second[pred_num] = ZERO;
  trans2.second[pred_num] = ONE;

  if (trans1.first[wp_pred_num] == NON_DET)
    {
      assert(trans1.first[wp_pred_num] == NON_DET);
      trans1.first[wp_pred_num] = ZERO;
      trans2.first[wp_pred_num] = ONE;
    }
  else
    {
      assert(trans1.first[wp_pred_num] == trans2.first[wp_pred_num]);
      if (trans1.first[wp_pred_num] == ONE)
	{
	  trans1.first.clear();
	  trans1.second.clear();
	}
      else
	{
	  trans2.first.clear();
	  trans2.second.clear();
	}
    }

  weakest_precondition_constrains.insert(std::pair<abstract_transition_constraintt, 
					 abstract_transition_constraintt> 
					 (trans1, trans2)) ;
}


/*******************************************************************\

Function: refinert::compute_wp_seed_predicate

  Inputs:

 Outputs:

 Purpose: Given a predicate and a bound takes wp till that bound.

\*******************************************************************/


void refinert::compute_wp_seed_predicate
 (predicatest &predicates, 
  const abstract_counterexamplet &spurious_counterexample,
  const symbol_tablet &symbol_table, 
  const network_infot &network,
  weakest_precondition_constrainst &weakest_precondition_constrains,
  unsigned pred_num, //we will take wp of this
  int len, //no. of steps for which to take the weakest pre-condition
  std::vector<std::set<unsigned> > &imp_preds_per_state,
  bool generate_extra_preds
  )
{
  namespacet ns(symbol_table);
  
  exprt failed_property(predicates[pred_num]);
  ns.follow_macros(failed_property);
  network.replace_outputs(failed_property);  

  std::set<predicatet> predicate_set;

  bool early_quit = false;

  for (int i=len; i >= 0 && (!early_quit); i--) {
    std::string code;

    exprt failed_property_copy(failed_property);
    std::set<unsigned> preds_used_to_simplify;
    bool containsInput = false; //failed_property should not have an input symbol.
                                // need to add quantifier intantiattion code
    
    network.simplified_weakest_precondition(failed_property, spurious_counterexample[i], 
					    predicates, preds_used_to_simplify, containsInput);

    simplify(failed_property, ns);

    //we want to avoid avoid adding new predicates as much as possible
    //this condition is true only when we fail to find new predicates...
    if (generate_extra_preds)
      imp_preds_per_state[i].insert(preds_used_to_simplify.begin(), preds_used_to_simplify.end());


    #ifdef DEBUG
    //    std::cout << "failed property " << failed_property << "\n";
    if (generate_extra_preds)
      std::cout << "Adding "<<preds_used_to_simplify << " imp_preds["<<i<<"]\n";
    std::cout <<"simplified_weakest_precondition is  \n"
	      << expr2verilog (failed_property) << " \n";
    std::cout <<"Discovering predicates in the intermediate weakest pre-cond containsInput "
	      <<containsInput<<"\n";
    #endif
    
    bool isAtomic = false;
    discover_predicates(failed_property, predicate_set, discover, isAtomic);
  
    #ifdef DEBUG
    std::cout << "predicates discovered \n";
    std::cout << predicate_set << "\n";
    #endif

    if (add_wp_cons) {
      if (isAtomic && !containsInput) {
	assert (predicate_set.size() == 1);
       	#ifdef DEBUG
	
	std::cout <<"An atomic predicate discovered: "
		  << expr2verilog (*predicate_set.begin())<<"\n";
	std::cout <<"Preds used in simplification \n";
	std::cout << preds_used_to_simplify;
        #endif
      }
      else if (isAtomic && containsInput) {
	#ifdef DEBUG
	std::cout << "Atomic but contains input \n";
        #endif
      }
      else {
	#ifdef DEBUG
	std::cout << "Not atomic  \n";
        #endif
      }
    }
    
    if(verbose)
      status() << "Before refinement #predicates " << predicates.size() << eom;
    

    for(std::set<predicatet>::const_iterator it= predicate_set.begin();
	it != predicate_set.end(); it++) 
      {
	#ifdef DEBUG
	std::cout << "Found predicate: "<< *it << "\n";
	#endif

 	if (containsSymbol(*it)) {
	  predicates.lookup(*it);
	  
	  if (add_wp_cons) { 
	    if (isAtomic && !containsInput) {
	      
	      //find the predicate number assigned to this predicate

	      unsigned nr_wp, nr_pred;
	      
	      if (predicates.find (failed_property_copy, nr_pred)) 
		{
		  if (predicates.find(*it, nr_wp)) 
		    {

		      relate_pred_and_wp
			(spurious_counterexample[i],
			 preds_used_to_simplify,
			 weakest_precondition_constrains,
			 nr_pred, nr_wp) ;
		    }
		}
	    }
	  }
	}
      }
    
    predicate_set.clear();
       

    if (!isAtomic || containsInput)
      {
        #if 0
	std::cout << "Early quiting isatomic " <<isAtomic << " containsinput "
		  <<containsInput<<"\n";
	if (isAtomic )
	  std::cout << expr2verilog(failed_property) << "\n";
        #endif

	early_quit = true;
      }

    if (verbose)
      status() << "After refinement #predicates " << predicates.size() << eom;


    
    if (failed_property.is_false() || 
	failed_property.is_true() ||
	!containsSymbol(failed_property))
      {
	#ifdef DEBUG
	std::cout <<"setting early quit to true as the property is constant true/false \n";
	#endif

	early_quit = true;
      }
  }
  
}



/*******************************************************************\

Function: refinert::generate_predicates

  Inputs:

 Outputs:

 Purpose:  

\*******************************************************************/


void refinert::generate_predicates
 (predicatest &predicates, 
  const abstract_counterexamplet &spurious_counterexample,
  const symbol_tablet &symbol_table, 
  const network_infot &network,
  std::vector<std::set<unsigned> > &imp_preds_per_state,
  weakest_precondition_constrainst &weakest_precondition_constrains,
  bool generate_extra_preds
  )
{
  for (unsigned i = imp_preds_per_state.size()-1; i >=1 ; i--) {
    
    for(std::set<unsigned>::const_iterator it= imp_preds_per_state[i].begin();
	it != imp_preds_per_state[i].end(); it++) {
      
      assert (*it >= 0);
      assert (*it < predicates.size());

      #ifdef DEBUG
      std::cout << "Now computing wp of predicate no. "<<*it <<"for "<<i-1<<" steps \n";
      #endif

      compute_wp_seed_predicate(predicates, 
				spurious_counterexample,
				symbol_table, 
				network,
				weakest_precondition_constrains,
				*it,
				i-1,
				imp_preds_per_state,
				generate_extra_preds);

      
    }
  }
}

/*******************************************************************\

Function: refinert::spurious_ce

  Inputs:

 Outputs:

 Purpose: generate a new set of predicates given a spurious counterexample

\*******************************************************************/


void refinert::spurious_ce
 (predicatest &predicates, 
  const concrete_transt &concrete_trans,
  const abstract_counterexamplet &spurious_counterexample,
  const symbol_tablet &symbol_table, 
  const exprt property,
  const network_infot &network,
  std::vector<std::set<unsigned> > &imp_preds_per_state,
  weakest_precondition_constrainst &weakest_precondition_constrains, //obtain the weakest pre-condition constraints
  bool generate_extra_preds
  )
 {
   if (verbose)
     status() << "Size of spurious counterexample "
              << spurious_counterexample.size() << eom;

   
   #ifdef DEBUG
   std::cout <<"Use unsat cores when computing the weakest pre-condition \n";	
   #endif

   generate_predicates(predicates, 
		       spurious_counterexample,
		       symbol_table, 
		       network,
		       imp_preds_per_state,
		       weakest_precondition_constrains, 
		       generate_extra_preds);



   if (verbose)
     {
       std::cout <<" After refinement \n";
       std::cout <<predicates;
     }

 }









