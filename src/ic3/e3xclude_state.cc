/******************************************************

Module:  Excludes a state from which a bad state is
         reachable (Part 3)

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

/*================================

      I N C R _ S H O R T

 ================================*/
void CompInfo::incr_short(CLAUSE &C,CLAUSE &C0,int curr_tf,
                          char st_descr,int rec_depth)
{

  if (verbose > 1) {
    printf("%*c",6,' ');
    printf("incr_short\n");
  }


  SatSolver &Slvr = Time_frames[curr_tf].Slvr; 
  int impr_count = 0;
  C = C0;
  if (C.size() == 1) return;

  CLAUSE Curr = C0;

  SCUBE Tried;
  SCUBE Failed_lits;

  size_t max_tries = 4;
  if (C0.size()  < max_tries) 
    max_tries = C0.size();
  size_t num_tries = 0;

  while (true) {
    if (num_tries > max_tries) 
      return;
    
    if (Curr.size() <= Tried.size())
      return;

    int lit = pick_lit_to_remove(Curr,Tried,curr_tf);

 // remove literal
   
    rem_lit(Curr,lit);
    Tried.insert(lit);
   
    bool ok = corr_clause(Curr);
    if (!ok) {
      Curr.push_back(lit);
      num_tries++;
      if (ctg_flag) Failed_lits.insert(lit);
      continue;
    }
       

    CLAUSE C1;
    if ((ctg_flag == false) || (curr_tf == 0)) {  
      if (grl_heur == NO_JOINS)
	ok = triv_ind_cls_proc(C1,Curr,curr_tf);
      else {
	assert(grl_heur == WITH_JOINS);
	ok = find_ind_subclause_cti(C1,Slvr,Curr,st_descr);
      }
    }
    else 
      ok =  find_ind_subclause_ctg(C1,curr_tf,Curr,st_descr,
                 rec_depth,Failed_lits);
 

    if (!ok) {
      failed_impr++;
      if (ctg_flag) Failed_lits.insert(lit);
      Curr.push_back(lit);
      num_tries++;
      continue;
    }

    succ_impr++;
 
    if (++impr_count > max_num_impr) max_num_impr = impr_count;
    C = C1;
    if (C.size() == 1) return;
    Curr = C1;
    num_tries = 0;
    Tried.clear();
    if (C1.size() < max_tries) max_tries = C1.size();
  }

} /* end of function incr_short */


/*============================================

         M O D I F _ L O C _ C L A U S E

   Currently local clause C excludes an initial
   state. This function expands clause C to 
   make it satisfy all initial states while 
   still excluding state St

  ASSUMPIONS:
    1) The set of initial states forms a cube

  ===========================================*/
void CompInfo::modif_loc_clause(CLAUSE &C,CUBE &St)
{

  if (verbose > 1) printf("correcting local clause\n");
  // find a variable where 'St' has the oposite
  // value of all initial states

  htable_lits.change_marker();
  htable_lits.started_using();

  int marker = htable_lits.marker;
  CUBE &Table = htable_lits.Table;

  for (size_t i=0; i < St.size(); i++) {
    int var_ind = abs(St[i])-1;
    if (St[i] < 0) Table[var_ind] = marker;
    else {
      assert(var_ind+max_num_vars < Table.size());
      Table[var_ind+max_num_vars] = marker;
    }
  }
  
  int lit = 0;
  for (size_t i=0; i < Ist.size(); i++) {
    CLAUSE &A = Ist[i];
    int var_ind = abs(A[0])-1;
    if ((Table[var_ind] == marker) && (A[0] > 0)) {
      lit = var_ind+1;
      break;}

    if ((Table[var_ind+max_num_vars] == marker) && (A[0] < 0)) {
      lit = -(var_ind+1);
      break;}
  }

  assert(lit != 0);
  C.push_back(lit);
  htable_lits.done_using();

} /* end of function modif_loc_clause */

/*========================================

        F O R M _ L N G S T _ C L A U S E

  =========================================*/
void form_lngst_clause(CLAUSE &C0,CUBE &St)
{

  for (size_t i=0; i < St.size(); i++) 
    C0.push_back(-St[i]);

} /* end of function form_lngst_clause */


/*==============================

    F I N D _ R A N D _ L I T

  ============================*/
int CompInfo::find_rand_lit(CLAUSE &Curr,SCUBE &Tried)
{

  while (true) {
    int ind = lrand48() % Curr.size();
    int lit = Curr[ind];
    if (Tried.find(lit) == Tried.end()) 
      return(lit);
  }
} /* end of function find_rand_lit */


/*=======================

       R E M _ L I T

  ======================*/
void CompInfo::rem_lit(CLAUSE &Curr,int lit) {

  bool found = false;
  for (size_t i=0; i < Curr.size(); i++) {
    if (Curr[i] == lit) {
      found = true;
      continue; }

    if (found) 
      Curr[i-1] = Curr[i];
  }
  assert(found);
  Curr.resize(Curr.size()-1);

} /* end of function rem_lit */
