/******************************************************

Module: Generalization of an inductive clause

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

/*==================================

     S H O R T E N _ C L A U S E

  =================================*/
void CompInfo::shorten_clause(CLAUSE &C,int curr_tf,CLAUSE &C0,char st_descr,
                              int rec_depth)
{

  assert(curr_tf>=0 && (size_t) curr_tf < Time_frames.size());
  CLAUSE B0 = C0;
  
  while (true) {
    if (B0.size() < 10) break;
    CLAUSE B;  
    compos_short(B,B0,curr_tf,st_descr);
    if (B.size() == B0.size()) break;
    B0 = B;   
    break;
  }

 
  incr_short(C,B0,curr_tf,st_descr,rec_depth);
 
} /* end of function shorten_clause */

/*=========================================

       A D D _ M I S S I N G _ L I T S

  ========================================*/
int CompInfo::add_missing_lits(CLAUSE &C,CLAUSE &B)
{

  SCUBE S;
  array_to_set(S,C);

  int count = 0;
  for (size_t i=0; i < B.size(); i++) 
    if (S.find(B[i]) == S.end()) {
	C.push_back(B[i]);
	count++;
      }

  return(count);    
} /* end of function add_missing_lits */

/*===========================================

        F I N D _ F I X E D _ P N T

  ============================================*/
void CompInfo::find_fixed_pnt(CLAUSE &C,CLAUSE &C0,SatSolver &Slvr,
                             char st_descr)
{

  while (true) {
    // add state related clauses
    Mlit act_lit;
    MvecLits Assmps;
    add_temp_clause(act_lit,Slvr,C);
    Assmps.push(act_lit);

    if (st_descr == NEW_STATE) add_negated_assumps2(Assmps,C0,false);
    else add_negated_assumps2(Assmps,C0,true);

    // run a SAT-check
         
    bool sat_form = check_sat2(Slvr,Assmps);
  
    assert(sat_form == false);
    CLAUSE B;
    gen_assump_clause(B,Slvr,Assmps);
    CLAUSE B1;
    conv_to_pres_state(B1,B);
    int num = add_missing_lits(C,B1);
    release_lit(Slvr,~act_lit);
    if (num == 0) break; // fixed point is reached
  }



} /* end of function find_fixed_pnt */

/*=============================

       R A N D _ I N I T

  ============================*/
void CompInfo::rand_init(CLAUSE &B,CUBE &Avail_lits,SCUBE &Tried_lits)
{
   
  while (true) {
    int ind = lrand48() % Avail_lits.size();
    int lit = Avail_lits[ind];
    if (Tried_lits.find(lit) != Tried_lits.end()) continue;
    Tried_lits.insert(lit);
    B.push_back(lit);
    break;
  }

} /* end of function rand_init */

/*======================================

     F I N D _ A V A I L _ L I T S

  ====================================*/
void CompInfo::find_avail_lits(CUBE &Avail_lits,CLAUSE &C)
{

  SCUBE S;
  for (size_t i=0; i < Ist.size(); i++) {
    assert(Ist[i].size() == 1);
    CLAUSE &U = Ist[i];
    S.insert(U[0]);
  }

  for (size_t i=0; i < C.size(); i++) 
    if (S.find(C[i]) != S.end())
      Avail_lits.push_back(C[i]);

} /* end of function find_avail_lits */

/*=====================================

        C O M P O S _ S H O R T

  ASSUMPTION: 
   1) Initial states are specified
      by a CNF consisting of unit 
      clauses

  ==================================*/
void CompInfo::compos_short(CLAUSE &C,CLAUSE &C0,int curr_tf,char st_descr)
{

  
  assert(curr_tf >= 0);
  assert((size_t) curr_tf < Time_frames.size());
  size_t num_tries = 0;
  C = C0;

  size_t max_num_tries = 3;

  CUBE Avail_lits;
  find_avail_lits(Avail_lits,C0); 
  assert(Avail_lits.size() > 0);
  if (max_num_tries > Avail_lits.size()) max_num_tries = Avail_lits.size();

  SCUBE Tried_lits;

  SatSolver &Slvr = Time_frames[curr_tf].Slvr;
  while (num_tries < max_num_tries) {
    CLAUSE B;
    switch (lit_pick_heur) {
    case RAND_LIT:
      rand_init(B,Avail_lits,Tried_lits);
      break;
    case INACT_LIT:
      act_lit_init(B,Avail_lits,Tried_lits,Lit_act0,Lit_act1);
      break;
    case INACT_VAR:
      act_var_init(B,Avail_lits,Tried_lits,Lit_act0,Lit_act1);
      break;
    case FIXED_ORDER:
      fxd_ord_init(B,Avail_lits,Tried_lits);
      break;
    default:
      assert(false);
    }

    find_fixed_pnt(B,C0,Slvr,st_descr);
   
    if (B.size() < C.size()) C = B;
    if (C.size() < 10) break;
    num_tries++;
  }


}/* end of function compos_short */




