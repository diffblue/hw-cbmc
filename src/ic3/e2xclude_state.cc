/******************************************************

Module:  Excludes a state from which a bad state is
         reachable (Part 2)

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

   F I N D _ I N D _ S U B C L A U S E _ C T I

  If (reset_flag == 'false'),
  Icb_sat is not reset when
  formula is unsatisfaible

  ==========================================*/
bool CompInfo::find_ind_subclause_cti(CLAUSE &C,SatSolver &Slvr,
                                      CLAUSE &C0,char st_descr)
{

  if (verbose > 2) {
    printf("%*c",6,' ');
    printf("find_ind_sub_clause_cti\n");
  }
  C = C0;


  // MAIN LOOP

  //int count = 0;
  while(true)  {
    // add assumptions
    MvecLits Assmps;
    Mlit act_lit;  
    add_temp_clause(act_lit,Slvr,C);
    Assmps.push(act_lit);

    if (st_descr == NEW_STATE) add_negated_assumps2(Assmps,C,false);
    else add_negated_assumps2(Assmps,C,true);

    // run a SAT-check
   
    bool sat_form = check_sat2(Slvr,Assmps);

  
    // inductive clause is found
    if (sat_form == false) {// C is the longest inductive clause
      CLAUSE C1,C2;
      gen_assump_clause(C1,Slvr,Assmps);
     
      conv_to_pres_state(C2,C1);
      if (!corr_clause(C2)) modif_ind_clause(C2,C);     
      C = C2;
      release_lit(Slvr,~act_lit);
      return(true);     
    }

    // inductive clause is not found yet
    CUBE St;
    extr_cut_assgns1(St,Pres_svars,Slvr);

    release_lit(Slvr,~act_lit);

    adjust_clause1(C,St);
    bool ok = corr_clause(C);
    if (!ok)  return(false);
   
  }
} /* end of function find_ind_subclause_cti */


/*===============================

      C O R R _ C L A U S E

   Returns 'true' if no initial
   state falsifies C. Otherwise,
  returns 'false'

   ASSUMPTIONS:
    The set of initial states forms
    a cube

  ===============================*/
bool CompInfo::corr_clause(CLAUSE &C)
{

  
  htable_lits.change_marker(); // increment or reset the hash table marker 
  htable_lits.started_using();

  int marker = htable_lits.marker;
  CUBE &Table = htable_lits.Table;

  for (int i=0; i < C.size(); i++) {
    int var_ind = abs(C[i])-1;
    if (C[i] < 0) Table[var_ind] = marker;
    else Table[var_ind+max_num_vars] = marker;
  }
  

  for (int i=0; i < Ist.size(); i++) {
    CLAUSE &A = Ist[i];
    int var_ind = abs(A[0])-1;
    if ((Table[var_ind] == marker) && (A[0] < 0)) {
      htable_lits.done_using();
      return(true);}

    if ((Table[var_ind+max_num_vars] == marker) && (A[0] > 0)) {
      htable_lits.done_using();
      return(true);}
  }

  htable_lits.done_using();
  return(false);

} /* end of function corr_clause */


/*=====================================

      A D J U S T _ C L A U S E 1

  This function remove the literals of C
  that are satisfied by 'St'. So on
  exit, clause C is falsified by 'St'

  ASSUMPTIONS: 
    St is a complete assignment. So the set
    of variables assigned in 'St' contains
    every variable of C.

  =====================================*/
void CompInfo::adjust_clause1(CLAUSE &C,CUBE &St)
{

  if (verbose > 3) {
    printf("%*c",9,' ');
    printf("expand_clause\n");
  }
  htable_lits.change_marker(); // increment or reset the hash table marker 
  htable_lits.started_using();

  int marker = htable_lits.marker;
  CUBE &Table = htable_lits.Table;

  for (int i=0; i < St.size(); i++) {
    int var_ind = abs(St[i])-1;
    if (St[i] < 0) Table[var_ind] = marker;
    else Table[var_ind+max_num_vars] = marker;
  }

  int shift = 0;
  for (int i=0; i < C.size(); i++) {
    int var_ind = abs(C[i])-1;
    if ((Table[var_ind] == marker) && (C[i] < 0)) {
      shift++;
      continue;}
    if ((Table[var_ind+max_num_vars] == marker) && (C[i] > 0)) {
      shift++;
      continue;}

    C[i-shift] = C[i];
  }

  if (shift == 0) {
    p();
    print_bnd_sets1();
    exit(1); }

  C.resize(C.size()-shift);
  htable_lits.done_using();

} /* end of function adjust_clause1 */


