/*******************************************************************\

Module: Performs pre-processing on the given verilog program and
        collects information which will be used later. Builds the
        network for a given circuit.

Author: Himanshu Jain

Date: July 2004

\*******************************************************************/

#ifndef CPROVER_NETWORK_INFO_H
#define CPROVER_NETWORK_INFO_H

#include <util/message.h>
#include <util/namespace.h>
#include <util/symbol_table_base.h>

#include <trans-netlist/var_map.h>
#include <verilog/expr2verilog.h>

#include "concrete_trans.h"
#include "abstract_trans.h"
#include "predicates.h"
#include "vcegar_util.h"
#include "abstract_counterexample.h"

class network_infot
{
  std::vector<std::set<irep_idt> > vector_symbolsets;
  std::vector<std::set<exprt> > vector_exprsets;
  next_state_function_cachet next_state_function_cache;
 
  const var_mapt &var_map;
  const symbol_table_baset &symbol_table;

  void create_network (const exprt& general_constrains,
		       std::vector<std::set<irep_idt> > &vector_symbolsets,
		       std::vector<std::set<exprt> > &vector_exprsets,
		       const var_mapt &var_map);


  void print_network (const std::vector<std::set<irep_idt> > &vector_symbolsets,
		      const std::vector<std::set<exprt> > &vector_exprsets,
		      const var_mapt &var_map);
  
  void print_symbolset (const std::set<irep_idt>  &symbolset,
			const var_mapt &var_map);
  
  void print_exprset (const std::set<exprt>  &exprset);
  
  void replace_outputs 
    (exprt& property,
     const std::vector<std::set<irep_idt> > &vector_symbolsets,
     const std::vector<std::set<exprt> > &vector_exprsets,
     const var_mapt &var_map) const;

  void build_next_state_function_cache
    (const exprt &trans_rel, 
     const std::vector<std::set<irep_idt> > &vector_symbolsets,
     const std::vector<std::set<exprt> > &vector_exprsets,
     const var_mapt &var_map,
     next_state_function_cachet &next_state_function_cache);

  void print_next_state_function_cache
    (const next_state_function_cachet &next_state_function_cache);

  void create (const exprt& constraints, 
	       const exprt& trans, 
	       const var_mapt& var_map);
  
  bool lookup (const std::vector<std::set<irep_idt> > &vector_symbolsets,
	       const irep_idt &name, unsigned& nr) const;
  
  void weakest_precondition_recur (exprt& property) const;

  void weakest_precondition_recur (exprt& property, const next_state_function_cachet &ns_cache) const;

  void weakest_precondition_recur_demand (const abstract_statet &abstract_state, 
					  const predicatest &predicates,
					  exprt& property, 
					  next_state_function_cachet &ns_cache,
					  std::set<unsigned> &preds_used_to_simplify,
					  bool &containsInput) const ;

 

 public:
   network_infot(
     const exprt &constraints,
     const exprt &trans,
     const var_mapt &_var_map,
     const symbol_table_baset &_symbol_table)
     : var_map(_var_map), symbol_table(_symbol_table)
   {
     create(constraints, trans, var_map);
    }
  
  ~network_infot() { }

  void print_members() ;

  void print_next_state_function_cache() ;
 
  void weakest_precondition (exprt& property) const ;
  
  void replace_outputs (exprt &property) const;

  void simplified_weakest_precondition (exprt  &property, 
					const abstract_statet &abstract_state, 
					const predicatest &predicates, 
					std::set<unsigned> &preds_used_to_simplify,
					bool &containsInput) const ;

  void build_next_state_function_cache
    (const exprt &trans_rel, 
     const std::vector<std::set<irep_idt> > &vector_symbolsets,
     const std::vector<std::set<exprt> > &vector_exprsets,
     const var_mapt &var_map,
     std::vector<std::set<exprt> > &outputs_replaced_definitions,
     next_state_function_cachet &next_state_function_cache);

  void replace_outputs 
    (const std::vector<std::set<irep_idt> > &vector_symbolsets,
     const std::vector<std::set<exprt> > &vector_exprsets,
     const var_mapt &var_map,
     std::vector<std::set<exprt> > &outputs_replaced_definitions, //kind of cache
     exprt& property) const;
};

#endif
