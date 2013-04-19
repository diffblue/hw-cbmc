/*******************************************************************\

Module: Utilities for VCEGAR

Author: Himanshu Jain

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_VCEGAR_UTIL_H
#define CPROVER_VCEGAR_UTIL_H

#include <sstream>

#include <message.h>
#include <context.h>
#include <expr.h>

#include <verilog/expr2verilog.h>
#include <trans/var_map.h>

#include "concrete_trans.h"
#include "abstract_trans.h"
#include "predicates.h"

typedef std::map<const std::string, exprt> next_state_function_cachet;
typedef std::map<const std::string, exprt> symbol_function_tablet;


void rename (exprt& current_pred);
  
std::ostream& operator<< (std::ostream& out,
			  const std::set<unsigned> &uint_set);

std::ostream& operator<< (std::ostream& out,
			  const literalt &lit);


unsigned max (const std::set<unsigned> &uint_set);


bool containsSymbol (const exprt &expr);


void get_next_state_function(
  std::string name, 
  const exprt &trans_rel, 
  exprt &definition);
   
void search_wire(
  std::string name,
  const exprt &trans_rel,
  exprt& definition,
  const var_mapt &var_map);
    
void search_input(
  std::string name, 
  const exprt &trans_rel,
  exprt& definition);
 
void replace_outputs(
  exprt& property,
  const exprt &general_constrains,
  const var_mapt &var_map);
   
void find_symbols(
  const exprt &predicate, 
  std::set<std::string>& symbols, 
  const std::string name);

bool subset
(const std::set<std::string>& set1,
 const std::set<std::string>& set2
 ) ;


void preds_from_case_assignments
(const exprt function, 
 const exprt variable_expr,
 std::set<exprt>& predicates
 );


void wp_with_predicates
(exprt& property,
 const exprt &trans_rel,
 const var_mapt &var_map,
 std::set<exprt> &predicates
 );
  
void simplify_expr (exprt& expr);    

void weakest_precondition
(exprt& property,
 const next_state_function_cachet& next_state_function_cache
 );

void weakest_precondition
(exprt& property,
 const exprt &trans_rel,
 const var_mapt &var_map);

void compute_pre_symbols 
(const std::set<std::string> &symbols,
 const exprt &trans_rel,
 const var_mapt& var_map,
 next_state_function_cachet &next_state_function_cache,
 symbol_function_tablet &symbol_function_table,
 std::set<std::string> &pre_symbols
 );

int get_type_integer(const var_mapt &vmap, const std::string &s);

std::ostream& operator<< (std::ostream& out,
			  const std::vector<std::set<unsigned> > &vec_vec_unsigned);

std::string double2string(const double& x);

#endif
