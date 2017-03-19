/**********************************************************

Module: A few procedures of sorting gates that affect
        the order of clauses in formulas (e.g. transition
        relation)

Author: Eugene Goldberg, eu.goldberg@gmail.com

**********************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>
#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

/*========================================

  G A T E _ S O R T _ O U T S _ F I R S T

 =========================================*/
void CompInfo::gate_sort_outs_first()
{

  DNF Level_gates;

  fill_up_levels(N,Level_gates);

  for (int i=Level_gates.size()-1; i >= 0; i--) {
    CUBE &Level = Level_gates[i];
 
    for (int j=0; j < Level.size();j++) 
      Ordering.push_back(Level[j]);
      
  }

  assert(N->Gate_list.size() == Ordering.size());

} /* end of function gate_sort_outs_first */


/*=======================================

 G A T E _ S O R T _ I N P S _ F I R S T

 ========================================*/
void CompInfo::gate_sort_inps_first()
{

  DNF Level_gates;

  fill_up_levels(N,Level_gates);

  for (int i=0; i < Level_gates.size(); i++) {
    CUBE &Level = Level_gates[i];
 
    for (int j=0; j < Level.size();j++) 
      Ordering.push_back(Level[j]);
      
  }

  assert(N->Gate_list.size() == Ordering.size());

} /* end of function gate_sort_inps_first */

/*=======================================

      R A N D _ G A T E _ O R D E R

  =======================================*/
void CompInfo::rand_gate_order()
{
  int count = N->Gate_list.size();

  int shift = N->ninputs + N->nlatches;
  int range = N->Gate_list.size() - shift;
  init_gate_order();
  while (count-- > 0) {
    int gate_ind1 = lrand48() % range;
    int gate_ind2 = lrand48() % range;
    if (gate_ind1 == gate_ind2) 
      if (gate_ind1 == 0) gate_ind2 = 1;
      else // gate_ind1 > 0
	gate_ind2 = gate_ind1 - 1;
    int copy = Ordering[gate_ind1];
    Ordering[gate_ind1] = Ordering[gate_ind2];
    Ordering[gate_ind2] = copy;
  }


} /* end of function rand_gate_order */


/*=======================================

      I N I T _ G A T E _ O R D E R

  =======================================*/
void CompInfo::init_gate_order()
{
  for (int i=0; i < N->Gate_list.size(); i++) 
    Ordering.push_back(i);

} /* end of function init_gate_order */

/*====================================

  O R D E R _ G A T E S

  =====================================*/
void CompInfo::order_gates()
{
  switch (gate_sort_mode) {
  case INIT_SORT:
    init_gate_order();
    return;
  case INPS_FIRST:
    gate_sort_inps_first();
    return;
  case OUTS_FIRST:
    gate_sort_outs_first();
    return;
  case RAND_SORT:
    rand_gate_order();
    return;
  default:
    assert(false);
  }

} /* end of function order_gates */

