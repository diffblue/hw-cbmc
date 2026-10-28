/******************************************************

Module:  Some auxiliary functions (Part 4)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
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


/*============================================

  A D D _ N E G A T E D _ A S S U M P S 2

  ASSUMPTION:
    1) Clause 'C' is specified in temrs of
       present state vars

 ============================================*/
void CompInfo::add_negated_assumps2(MvecLits &Assmps,CLAUSE &C,bool sort)
{
 
  CLAUSE Cn;
  if (ind_cls_sort_mode == NO_SORT) {   
    conv_to_next_state(Cn,C);
    add_negated_assumps1(Assmps,Cn);
    return; }


  CLAUSE C1; 
  if (sort)  
     sort_in_activity(C1,C,ind_cls_sort_mode,false);
  else C1 = C;
  
  conv_to_next_state(Cn,C1);
  add_negated_assumps1(Assmps,Cn);
  

} /* end of function add_negated_assumps2 */

/*===========================================

     A D D _ N E G A T E D _ A S S U M P S 1

  ==========================================*/
void CompInfo::add_negated_assumps1(MvecLits &Assmps,CLAUSE &C)
{

  for (size_t i=0; i < C.size(); i++) {
    int lit = C[i];
    if (lit < 0) Assmps.push(IctMinisat::mkLit(-lit-1,false));
    else Assmps.push(IctMinisat::mkLit(lit-1,true));
  }
    
} /* end of function add_negated_assumps1 */

/*=================================

      R E L E A S E _ L I T 

 =================================*/
void CompInfo::release_lit(SatSolver &Slvr,Mlit lit)
{

  Slvr.Mst->releaseVar(lit);
  Slvr.num_rel_vars++;

} /* end of function release_lit */


/*=============================

     A D D _ A S S U M P S 2 

  ============================*/
void CompInfo::add_assumps2(MvecLits &Assmps,CUBE &St)
{

  if (lift_sort_mode == NO_SORT) {
    add_assumps1(Assmps,St);
    return;
  }

  CUBE St1;
  sort_in_activity(St1,St,lift_sort_mode,false);
  add_assumps1(Assmps,St1);
} /* end of function add_assumps2 */

/*=============================

     A D D _ A S S U M P S 3

  ============================*/
void CompInfo::add_assumps3(MvecLits &Assmps,CUBE &St)
{

  for (int i=St.size()-1; i >= 0; i--) {
    int lit = St[i];
    if (lit < 0) Assmps.push(IctMinisat::mkLit(-lit-1,true));
    else Assmps.push(IctMinisat::mkLit(lit-1,false));
  }
    
} /* end of function add_assumps3 */


/*=============================

     A D D _ A S S U M P S 1 

  ============================*/
void CompInfo::add_assumps1(MvecLits &Assmps,CUBE &St)
{

  for (size_t i=0; i < St.size(); i++) {
    int lit = St[i];
    if (lit < 0) Assmps.push(IctMinisat::mkLit(-lit-1,true));
    else Assmps.push(IctMinisat::mkLit(lit-1,false));
  }
    
} /* end of function add_assumps1 */



/*======================================

    S O R T _ I N _ A C T I V I T Y

========================================*/
void CompInfo::sort_in_activity(CLAUSE &C1,CLAUSE &C,int sort_mode,bool reverse)
{

  //  form pairs
  std::vector <ActInd> V;

  for (size_t i=0; i < C.size(); i++) {
    float act_value;
    int var_ind = abs(C[i])-1;
    if (sorted_objects == LITS) {
      if (C[i] < 0) act_value = Lit_act0[var_ind];
      else act_value = Lit_act1[var_ind];
    }
    else if (sorted_objects == VARS) 
      act_value = Lit_act0[var_ind] + Lit_act1[var_ind];
    else assert(false);

    V.push_back(std::make_pair(act_value,i));
  }

  if (reverse) stable_sort(V.begin(),V.end(),sel_least_act());
  else stable_sort(V.begin(),V.end(),sel_most_act());
  

  if (sort_mode == FULL_SORT) full_sort(C1,C,V);
  else {
    assert(sort_mode == PART_SORT);
    part_sort(C1,C,V);}
  
  if (lit_pick_heur == RAND_LIT) 
    scale_factor_down(V.back().first);

} /* end of function sort_in_activity */

/*=======================================

        F U L L _ S O R T

  ========================================*/
void CompInfo::full_sort(CLAUSE &C1,CLAUSE &C, std::vector <ActInd> &V) {

  C1.assign(C.size(),0);
  for (size_t i=0; i < V.size(); i++) {
    int old_ind = V[i].second;
    C1[i] = C[old_ind];
  }
} /* end of function full_sort */


/*===================================

     P U S H _ O N _ T H E _ F L Y

  =================================*/
int CompInfo::push_on_the_fly(int last_ind,CLAUSE &C,char st_desc)
{

  int tf_ind = latest_succ_tf_ind(last_ind,C);
  if (tf_ind < 0) tf_ind = last_ind-1;

  return(tf_ind+1);

} /* end of function push_on_the_fly */
