/*******************************************************************\

Module: Routines for predicate partitioning

Author: Himanshu Jain

Date: June 2004

\*******************************************************************/

#ifndef CPROVER_PARTITIONING_H
#define CPROVER_PARTITIONING_H

#include <util/message.h>
#include <util/namespace.h>

#include <trans-netlist/var_map.h>
#include <verilog/expr2verilog.h>

#include "concrete_trans.h"
#include "abstract_trans.h"
#include "predicates.h"
#include "network_info.h"

class partitioningt
 {
 public:
   partitioningt()
     {

     }

   ~partitioningt()
     {

     }


   typedef std::map<exprt, std::set<std::string> > 
     predicate_symbol_mapt;

   typedef std::vector<predicatest>
     predicate_clusterst;

   typedef std::pair<std::set<unsigned>, std::set<unsigned> > 
     pred_id_set_pairt;


   typedef std::set<pred_id_set_pairt> 
     pred_id_clusterst;


    typedef std::map<exprt, unsigned> 
      predicate_index_mapt;
    

    typedef std::map<std::set<std::string>, 
      predicatest> symbolset_predicates_mapt;

    void print_clusters(const partitioningt::pred_id_clusterst 
			&refine_clusters) ;


    void print_predicate_symbol_maps 
      (
       const predicate_symbol_mapt& initial_predicates,
       const predicate_symbol_mapt& final_predicates
       );

    void print_predicate_clusters(const predicate_clusterst 
				  &pred_clusters);

    unsigned return_predicate_index
      (const predicate_index_mapt& predicate_index_map,
       const exprt& expr
       ) ;


    void partitioningA
      (const predicate_symbol_mapt& inputs,
      const predicate_symbol_mapt& finals,
       const predicate_index_mapt& pred_index_map, 
       predicate_clusterst& pred_clusters
       );
    

    void partition_predicates
      (const predicatest& predicates, 
      const exprt& trans,
       const namespacet &ns,
       const var_mapt& var_map,
       const network_infot &network,
       predicate_clusterst& pred_clusters,
       unsigned choice,
       bool verbose);
    
    void partition_initial_predicates
      (const predicatest& predicates, 
       const namespacet &ns,
       const exprt& trans,
       const var_mapt& var_map,
       const network_infot &network,
       predicate_clusterst& pred_clusters);
    
    void partitioningB
      (const predicate_symbol_mapt& inputs,
       const predicate_symbol_mapt& finals,
	const predicate_index_mapt& pred_index_map,
	 predicate_clusterst& pred_clusters
       );

    void monolithic
      (const predicate_symbol_mapt& inputs, 
       const predicate_symbol_mapt& finals,
       const predicate_index_mapt& pred_index_map,
       predicate_clusterst& pred_clusters
       );

    void partitioningC
      (const predicate_symbol_mapt& inputs, 
       const predicate_symbol_mapt& finals,
       const  predicate_symbol_mapt& final_only_symbols,
       const predicate_index_mapt& pred_index_map,
       predicate_clusterst& pred_clusters
       );

    void partitioningD
      (const  predicate_symbol_mapt& final_only_symbols,
       const predicate_index_mapt& pred_index_map,
       predicate_clusterst& pred_clusters
       );

    void partitioningE
      (const predicate_symbol_mapt& final_only_symbols,
       const predicate_index_mapt& pred_index_map,
       predicate_clusterst& pred_clusters);

    void activate_refinement_clusters
      (const predicatest& predicates,
       const network_infot &network,
       const namespacet &ns,
       const pred_id_clusterst &pred_id_clusters,
       predicate_clusterst& pred_clusters
       );


    void obtain_refinement_cluster
      (const predicatest& predicates,
       const network_infot &network,
       const namespacet &ns,
       const pred_id_set_pairt &pred_id_set_pair,
       predicatest& pred_cluster);

 };

#endif
