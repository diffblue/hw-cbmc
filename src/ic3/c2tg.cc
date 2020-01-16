/*********************************************************

Module: Computes an inductive clause excluding a counter-
        example to generalization (Part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com

*********************************************************/
#include <iostream>
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

/*======================================

      E X C L U D E _ S T G


  ASSUMPTIONS:

   1) 'St' does not contain an initial
      state
 =======================================*/
bool CompInfo::exclude_ctg(CUBE &St,int curr_tf,int rec_depth)
{
  
  CLAUSE C0;
  form_lngst_clause(C0,St);
  bool ok = corr_clause(C0);
  if (!ok) return(false);

  assert(curr_tf > 0);

  ok = triv_ind_cls(curr_tf-1,C0);
  if (!ok) return(false);

  int tf_ind = latest_succ_tf_ind(curr_tf,C0);
  if (tf_ind < 0) tf_ind = curr_tf-1;
  
  

  CLAUSE C1;
  
  shorten_clause(C1,tf_ind,C0,CTG_STATE,rec_depth+1);
 
  add_fclause1(C1,tf_ind+1,CTG_STATE);
  return(true);
 
} /* end of function exclude_ctg */

/*=======================================

   L A T E S T _ S U C C _ T F _ I N D

  ======================================*/
int CompInfo::latest_succ_tf_ind(int tf_ind,CLAUSE &C)
{

  int result = -1;

  for (int i= tf_ind; i <= tf_lind; i++) {
    bool ok = triv_ind_cls(i,C);
    if (!ok) return(result);
    result = i;}  

  return(tf_lind);
} /* end of function latest_succ_tf_ind */

/*=======================================

         F O R M _ N X T _ C U B E

  =====================================*/
void CompInfo::form_nxt_cube(CUBE &Nxt_cube,CLAUSE &C)
{

  for (size_t i=0;i < C.size(); i++) {
    int var_ind = abs(C[i])-1;
    int nxt_var_ind = Pres_to_next[var_ind];
    assert(nxt_var_ind >=0);
    int lit = (C[i] > 0)?-(nxt_var_ind+1):(nxt_var_ind+1);
    Nxt_cube.push_back(lit);
  }

} /* end of function form_nxt_cube */
