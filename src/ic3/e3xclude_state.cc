/******************************************************

Module:  Excludes a state from which a bad state is
         reachable (Part 3)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include "Solver.h"
#include "SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"


/*==========================

  I N C R _ S H O R T

  =========================*/
void CompInfo::incr_short(CLAUSE &C,int curr_tf,CLAUSE &C0,char st_descr)
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
  int max_tries = 4;
  if (C0.size()  < max_tries) 
    max_tries = C0.size();
  int num_tries = 0;

  
  while (true) {
  
    if (num_tries > max_tries)
      return;

    if (Curr.size() == Tried.size()) return;

   
    int lit;
    switch (lit_pick_heur) {
    case RAND_LIT:
      lit = find_rand_lit(Curr,Tried);
      break;
    case INACT_LIT:
      lit = find_inact_lit(Curr,Tried,Lit_act0,Lit_act1);
      break;
    case INACT_VAR:
      lit = find_inact_var(Curr,Tried,Lit_act0,Lit_act1);
      break;
    case RECENT_LITS:
      comput_rec_lit_act(curr_tf);
      lit = find_inact_var(Curr,Tried,Tmp_act0,Tmp_act1);
      break;
    case MIXED:
      if (Time_frames.size() < cut_off_tf) lit = find_rand_lit(Curr,Tried);
      else lit = find_inact_var(Curr,Tried,Lit_act0,Lit_act1);
      break;
    default:
      printf("lit_pick_heur = %d\n",lit_pick_heur);
      exit(100);
    }

    // remove literal
    rem_lit(Curr,lit);
    Tried.insert(lit);
    bool ok = corr_clause(Curr);
    if (!ok) {
      Curr.push_back(lit);
      num_tries++;
      continue;
    }
    
    CLAUSE C1;
    ok = lngst_ind_clause(C1,Slvr,Curr,st_descr); 
    if (!ok) {
      failed_impr++;
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

  htable_lits.change_marker(); // increment or reset the hash table marker 
  htable_lits.started_using();

  int marker = htable_lits.marker;
  CUBE &Table = htable_lits.Table;

  for (int i=0; i < St.size(); i++) {
    int var_ind = abs(St[i])-1;
    if (St[i] < 0) Table[var_ind] = marker;
    else {
      assert(var_ind+max_num_vars < Table.size());
      Table[var_ind+max_num_vars] = marker;
    }
  }
  
  int lit = 0;
  for (int i=0; i < Ist.size(); i++) {
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

  for (int i=0; i < St.size(); i++) 
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
  for (int i=0; i < Curr.size(); i++) {
    if (Curr[i] == lit) {
      found = true;
      continue; }

    if (found) 
      Curr[i-1] = Curr[i];
  }
  assert(found);
  Curr.resize(Curr.size()-1);

} /* end of function rem_lit */
