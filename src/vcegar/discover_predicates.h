/*******************************************************************\

Module: Predicate Discovery

Author: Daniel Kroening, kroening@kroening.com
                
\*******************************************************************/

#ifndef CPROVER_DISCOVER_PREDICATES_H
#define CPROVER_DISCOVER_PREDICATES_H

#include <verilog/expr2verilog.h>

#include "predicates.h"

#include <set>

void discover_predicates(const exprt &expr,
                         std::set<predicatet> &predicates, 
			 int choice, bool &isAtomic);

void discover_simple_preds_simplified(const exprt &expr,
				      std::set<predicatet> &predicates,
				      bool canonicalized,
				      bool &isAtomic);

#endif
