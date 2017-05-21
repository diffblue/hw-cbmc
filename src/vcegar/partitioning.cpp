/*******************************************************************\

Module: Partitioning (partitioning of predicates)

Author: Himanshu Jain

Date: April 2004

\*******************************************************************/

#include <cassert>
#include <map>
#include <vector>

#include <util/namespace.h>

#include <verilog/expr2verilog.h>

#include "partitioning.h"
#include "canonicalize.h"
#include "vcegar_util.h"

/*******************************************************************\

Function: print_predicate_symbol_maps

  Inputs:

 Outputs:

 Purpose: Useful for debugging

\*******************************************************************/

void partitioningt::print_predicate_symbol_maps(
  const predicate_symbol_mapt& initial_predicates,
  const predicate_symbol_mapt& final_predicates) 
{
  std::cout <<"Initial predicates and symbols in them \n";
  
  unsigned i=0;
  for (predicate_symbol_mapt::const_iterator 
	it = initial_predicates.begin(); 
      it != initial_predicates.end(); it++){
   

   std::cout <<"Predicate ["<< i <<"] \n"<<  expr2verilog(it->first) <<"\n";
   std::cout <<"Symbols \n";
   
   for (std::set<std::string>::const_iterator it2= it->second.begin();
	it2!= it->second.end(); it2++) {
     
     std::cout <<"  "<<*it2<<"\n";
   }

   std::cout <<"---------------\n";
   i++;
 }

 std::cout <<"Final predicates and symbols in them \n";
 
 i=0;
 
 for (predicate_symbol_mapt::const_iterator 
	it = final_predicates.begin(); 
      it != final_predicates.end(); it++){
   

   std::cout <<"Predicate ["<< i <<"] \n"<<  expr2verilog(it->first) <<"\n";
   
   std::cout <<"Symbols \n";
   
   for (std::set<std::string>::const_iterator it2= it->second.begin();
	it2!= it->second.end(); it2++) {
     
     std::cout <<"  "<<*it2<<"\n";
   }
   std::cout <<"---------------\n";
      i++;
 }
}

/*******************************************************************\

Function: print_predicate_clusters

  Inputs:

 Outputs:

 Purpose: Prints the various clusters of the predicates.

\*******************************************************************/

void partitioningt::print_predicate_clusters(const predicate_clusterst &pred_clusters)
{
  unsigned i=0;
  for (predicate_clusterst::const_iterator it3 = pred_clusters.begin();
       it3 != pred_clusters.end(); it3++) {
    
    std::cout << "Cluster no. "<<i<<"\n";
    std::cout <<*it3;
    i++;
  }
}


/*******************************************************************\

Function: partition_initial_predicates

  Inputs:

 Outputs:

 Purpose: Partitions the current set of predicates, for the calculation 
of initial set of states.

\*******************************************************************/
unsigned partitioningt::return_predicate_index
(const predicate_index_mapt& predicate_index_map,
 const exprt& expr
 ) 
{
  predicate_index_mapt::const_iterator sit =
    predicate_index_map.find(expr);
  
  if (sit == predicate_index_map.end())
    assert(0);

  return sit->second;

}


/*******************************************************************\

Function: partition_predicates

  Inputs:

 Outputs:

 Purpose: Given a set of current set of predicates, it first computes the next state
set of predicates. This is followed by placing each next state predicate into a 
new cluster together with the current state predicates which are identified using
weakest precondition of the next state predicate (partitioningA strategy).

\*******************************************************************/

void partitioningt::partition_predicates(
  const predicatest& predicates, 
  const exprt& trans,
  const namespacet &ns,
  const var_mapt& varmap,
  const network_infot &network,
  predicate_clusterst& pred_clusters,
  unsigned choice,
  bool verbose)
{   
  if (choice == 8)
    return;

  predicate_symbol_mapt initial_predicates, final_predicates;
  predicate_index_mapt predicate_index_map;


  if (!( choice == 2 ||
	 choice==6  || choice==4))
    throw "--partition option takes only one of 2,4 (monolithic) ,6, 8 as values\n";

 for(unsigned i=0; i<predicates.size(); i++) //No test is made to test if the value
    {                                         //of a predicate does not change.    
      if (!(choice==6 ||choice==7)){
	exprt input(predicates[i]);
        
 	ns.follow_macros(input);


	exprt input_copy(input); 
	//replace_outputs(input, (trans.operands())[0], varmap);
 	
	network.replace_outputs (input);

	std::set<std::string> input_symbols;
	find_symbols(input, input_symbols, "symbol");


	initial_predicates.insert(std::pair<exprt, std::set<std::string> >
				  (input_copy, input_symbols));
	predicate_index_map.insert(std::pair<exprt, unsigned >
				   (input_copy, i));


      }
      

      exprt final(predicates[i]); 


      ns.follow_macros(final);


      exprt final1(final); // need many copies :(

  
      network.replace_outputs(final);


      exprt final_copy(final);


      if (choice != 6 && choice != 7) {

  
	network.weakest_precondition (final_copy);
    }
      
      if (!(choice==3 || choice==6 || choice==7)) {

	network.replace_outputs (final_copy) ;
      }

      std::set<std::string> final_symbols;
      find_symbols(final_copy, final_symbols, "symbol");
      

      rename(final1);
      final_predicates.insert(std::pair<exprt, std::set<std::string> >
			      (final1, final_symbols));
      predicate_index_map.insert(std::pair<exprt, unsigned >
				 (final1, i));

    }

 #if 0
 print_predicate_symbol_maps(initial_predicates, final_predicates);
 #endif

 switch(choice){
 case 2: {
   if (verbose)
     std::cout <<"Calling partitioning strategyB : option 2\n";
   partitioningB(initial_predicates, final_predicates, 
		 predicate_index_map, pred_clusters);
   break;
 }
 case 4: { //monolithic, only one cluster is created.
   if (verbose)
     std::cout <<"Calling monolithic (no predicate partitioning) : option 4\n";
   monolithic(initial_predicates, final_predicates, 
	      predicate_index_map, pred_clusters);
   break;
 }
 case 6: {
   if (verbose)
     std::cout <<"Calling partitioning strategyD: option 6\n";
   partitioningD(final_predicates, 
		 predicate_index_map, pred_clusters);
   break;     
 }
 default:
   throw "Must not reach here\n";
 }
 
}

/*******************************************************************\

Function: partition_initial_predicates

  Inputs:

 Outputs:

 Purpose: Partitions the current set of predicates, for the calculation 
of initial set of states.

\*******************************************************************/
void partitioningt::partition_initial_predicates
(const predicatest& predicates, 
 const namespacet &ns,
 const exprt& trans,
 const var_mapt& varmap,
 const network_infot &network,
 predicate_clusterst& pred_clusters
 )
{   
  predicate_symbol_mapt initial_predicates;
  predicate_index_mapt predicate_index_map;

 for(unsigned i=0; i<predicates.size(); i++) 
    {                                        
      exprt input(predicates[i]); 
      ns.follow_macros(input);
      
      network.replace_outputs ( input );


      std::set<std::string> input_symbols;
      find_symbols(input, input_symbols, "symbol");


      exprt input1(predicates[i]);
      ns.follow_macros(input1);
      initial_predicates.insert(std::pair<exprt, std::set<std::string> >
				(input1, input_symbols));
      predicate_index_map.insert(std::pair<exprt, unsigned >
				 (input1, i));
      

    }


 
 //Trying to club the predicates sharing same symbols.
 //Hopefully! not many share the same symbols. 
 
 //which pred is mapped to which cluster
 unsigned pred_cluster_map[predicates.size()];
   
   unsigned predno=0;

   predicate_symbol_mapt::const_iterator 
     it = initial_predicates.begin();
   
   pred_clusters.reserve(predicates.size());

   while (it !=  initial_predicates.end()) {

     pred_clusters.push_back(predicatest());

     exprt p(it->first);
     
     unsigned index = return_predicate_index(predicate_index_map, p);

     pred_clusters[pred_clusters.size()-1].lookup(p, index, 
						  predicatest::INITIAL);
     
     pred_cluster_map[predno] = pred_clusters.size()-1;

     predno++;
     
     bool continue_scan = true;
     
     it++;
     while (it != initial_predicates.end() && continue_scan) {
       unsigned count =0;
       bool subset_found = false;
       
       for (predicate_symbol_mapt::const_iterator 
	      it1 = initial_predicates.begin();
	    it1 != it && (!subset_found) ; it1++)
	 {

	   if (subset(it->second, it1->second)) {
	     exprt p(it->first);
	     
	     unsigned index = return_predicate_index(predicate_index_map, p);
	     pred_clusters[pred_cluster_map[count]].lookup(p, index, 
							   predicatest::INITIAL);
	     

	     pred_cluster_map[predno] = pred_cluster_map[count];
	     predno++;
	     subset_found = true;
	   }
	   count++;
	 }
       
       if (subset_found) 
	 it++; 
       else
	 continue_scan=false;
       
     }
   
   }
}



/*******************************************************************\

Function:  partitioningB

Inputs: 

Outputs:

Purpose: Merges all final state predicates which have same symbols in
the weakest preconditions.

\*******************************************************************/


void partitioningt::partitioningB
(const predicate_symbol_mapt& inputs, 
 const predicate_symbol_mapt& finals,
 const predicate_index_mapt& pred_index_map,
 predicate_clusterst& pred_clusters
 )
{
  symbolset_predicates_mapt symbolset_predicates_map;
  //Add the symbol set associated with each next state predicate.

  for (predicate_symbol_mapt::const_iterator 
	 it1 = finals.begin();it1 != finals.end(); it1++)
    {
      exprt p(it1->first);

      symbolset_predicates_mapt::iterator it2 = 
	symbolset_predicates_map.find(it1->second);

      if (it2 == symbolset_predicates_map.end()) {
	symbolset_predicates_map.insert
	  (std::pair<std::set<std::string>, predicatest> 
	   (it1->second, predicatest()));

	symbolset_predicates_mapt::iterator it3 = 
	  symbolset_predicates_map.find(it1->second);
	
	unsigned index = return_predicate_index(pred_index_map, p);
	(it3->second).lookup(p, 
			     index,
			     predicatest::FINAL);

      }
      else {
	unsigned index = return_predicate_index(pred_index_map, p);
	(it2->second).lookup(p, 
			     index,
			     predicatest::FINAL);
      }
    }
  
  unsigned i =0;

  for(symbolset_predicates_mapt::iterator it1 = 
	symbolset_predicates_map.begin();
      it1 != symbolset_predicates_map.end(); it1++) {


    for (predicate_symbol_mapt::const_iterator 
	   it2 = inputs.begin();it2 != inputs.end(); it2++)
      {
	if (subset(it2->second, it1->first)) {
	  exprt p(it2->first);

	  unsigned index = return_predicate_index(pred_index_map, p);

	  (it1->second).lookup(p, index, 
			       predicatest::INITIAL);
	}
      }
    
  }
  
  i=0;
  
  for (i=0; i<symbolset_predicates_map.size(); i++)
    pred_clusters.push_back(predicatest());
   

  i=0;
  for(symbolset_predicates_mapt::const_iterator it = 
	symbolset_predicates_map.begin();
      it != symbolset_predicates_map.end(); it++) {
    for(unsigned j =0; j < (it->second).size(); j++) 
      {
	predicatest::statet state;
	unsigned nr;
	(it->second).get_info((it->second)[j], nr, state);
	exprt new_exprt((it->second)[j]);


	pred_clusters[i].lookup(new_exprt, nr, state); 
      }
    
    

    i++;
  }

}

/*******************************************************************\

Function:  monolithic

Inputs: 

Outputs:

Purpose: Puts all initial and final predicates in one cluster.

\*******************************************************************/


void partitioningt::monolithic
(const predicate_symbol_mapt& inputs, 
 const predicate_symbol_mapt& finals,
 const predicate_index_mapt& pred_index_map,
 predicate_clusterst& pred_clusters
 )
{
  pred_clusters.push_back(predicatest());
  
  //add all initial state predicates

  for (predicate_symbol_mapt::const_iterator 
	 it2 = inputs.begin();it2 != inputs.end(); it2++)
      {
	exprt p(it2->first);
	unsigned index = return_predicate_index(pred_index_map, p);
	pred_clusters[0].lookup(p, index, predicatest::INITIAL);
      }
  
  //add all final state predicates
  
  for (predicate_symbol_mapt::const_iterator 
	 it2 = finals.begin();it2 != finals.end(); it2++)
    {
      exprt p(it2->first);
      unsigned index = return_predicate_index(pred_index_map, p);
      pred_clusters[0].lookup(p, index, predicatest::FINAL);
    }

  return;
}


/*******************************************************************\

Function:  partitioningD

Inputs: 

Outputs:

Purpose: Merges all final state predicates which have same symbols. No input
preds are kept in the cluster. Very coarse partitioning.

\*******************************************************************/

void partitioningt::partitioningD
(const  predicate_symbol_mapt& final_only_symbols,
 const predicate_index_mapt& pred_index_map,
 predicate_clusterst& pred_clusters
 )
{
  symbolset_predicates_mapt symbolset_predicates_map;

  //first cluster the final state predicates.
  
  for (predicate_symbol_mapt::const_iterator 
	 it1 = final_only_symbols.begin(); 
       it1 != final_only_symbols.end(); it1++)
    {
      exprt p(it1->first);

      symbolset_predicates_mapt::iterator it2 = 
	symbolset_predicates_map.find(it1->second);

      if (it2 == symbolset_predicates_map.end()) {
	symbolset_predicates_map.insert
	  (std::pair<std::set<std::string>, predicatest> 
	   (it1->second, predicatest()));

	symbolset_predicates_mapt::iterator it3 = 
	  symbolset_predicates_map.find(it1->second);
	
	unsigned index = return_predicate_index(pred_index_map, p);
	(it3->second).lookup(p, 
			     index,
			     predicatest::FINAL);

      }
      else {
	unsigned index = return_predicate_index(pred_index_map, p);
	(it2->second).lookup(p, 
			     index,
			     predicatest::FINAL);
      }
    }
  
  
  unsigned  i=0;
  
  for (i=0; i<symbolset_predicates_map.size(); i++)
    pred_clusters.push_back(predicatest());
   

  i=0;
  for(symbolset_predicates_mapt::const_iterator it = 
	symbolset_predicates_map.begin();
      it != symbolset_predicates_map.end(); it++) {
    for(unsigned j =0; j < (it->second).size(); j++) 
      {
	predicatest::statet state;
	unsigned nr;
	(it->second).get_info((it->second)[j], nr, state);
	exprt new_exprt((it->second)[j]);


	pred_clusters[i].lookup(new_exprt, nr, state); 
      }
    
    i++;
  }

}


/*******************************************************************\

Function: vcegar_loopt::obtain_refinement_cluster

  Inputs:

 Outputs:

 Purpose: Copies predicate clusters to abstraction.refinement_clusters

\*******************************************************************/

void partitioningt::obtain_refinement_cluster
(const predicatest& predicates,
 const network_infot &network,
 const namespacet &ns,
 const pred_id_set_pairt &pred_id_set_pair,
 predicatest& pred_cluster)
{
  //add initial state preds
  
  for (std::set<unsigned>::const_iterator isp = (pred_id_set_pair.first).begin();
       isp != (pred_id_set_pair.first).end(); isp++)
    {
      unsigned pred_num = *isp;

      exprt input(predicates[pred_num]);
      ns.follow_macros(input);
      network.replace_outputs (input);
      
      pred_cluster.lookup(input, pred_num, predicatest::INITIAL);
    }
  
      //add final state preds

  for (std::set<unsigned>::const_iterator fsp = (pred_id_set_pair.second).begin();
       fsp != (pred_id_set_pair.second).end(); fsp++)
    {
      unsigned pred_num = *fsp;
      
      exprt final(predicates[pred_num]);
      ns.follow_macros(final);
      rename(final);
      network.replace_outputs (final);

      pred_cluster.lookup(final, pred_num, predicatest::FINAL);
    }
}




/*******************************************************************\

Function: vcegar_loopt::copy_clusters

  Inputs:

 Outputs:

 Purpose: Copies predicate clusters to abstraction.refinement_clusters

\*******************************************************************/


void partitioningt::print_clusters(const partitioningt::pred_id_clusterst 
				   &refine_clusters) 
{

  unsigned count = 0;
  
  for (partitioningt::pred_id_clusterst::const_iterator  it = refine_clusters.begin();
       it != refine_clusters.end(); it++)
    {
      std::cout << "Cluster num[" << count << "]: ";
      std::cout << it -> first;
      std::cout << it -> second;
    }
}

