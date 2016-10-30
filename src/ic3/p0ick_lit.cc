/******************************************************

Module:  Picking a literal to remove when generalizing
         an inductive clause (Part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>
#include "Solver.h"
#include "SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"



/*=============================

  A C T _ L I T _ I N I T 

  ============================*/
void CompInfo::act_lit_init(CLAUSE &B,CUBE &Avail_lits,SCUBE &Tried,
                            FltCube &Act0,FltCube &Act1)
{
 

  float max_act_lit;
  int max_lit = 0;

  for (int i=0; i < Avail_lits.size(); i++) {
    int lit = Avail_lits[i];
    if (Tried.find(lit) != Tried.end()) continue;    
    int var_ind = abs(lit)-1;

    if (max_lit == 0) { 
      max_lit = lit;
      if (lit < 0) max_act_lit = Act0[var_ind];
      else max_act_lit = Act1[var_ind];
      continue;
    }

    if (lit < 0) {
      if (Act0[var_ind] > max_act_lit) {
	max_act_lit = Act0[var_ind];
	max_lit = lit; }}
    else 
      if (Act1[var_ind] > max_act_lit) {
	max_act_lit = Act1[var_ind];
	max_lit = lit;}
  }


  assert(max_lit != 0);
  B.push_back(max_lit);


} /* end of function act_lit_init */

/*=============================

  A C T _ V A R  _ I N I T 

  ============================*/
void CompInfo::act_var_init(CLAUSE &B,CUBE &Avail_lits,SCUBE &Tried,
                            FltCube &Act0,FltCube &Act1)
{
  
 
  float max_act_var;
  int max_lit = 0;
  int count_eq = 0;

  for (int i=0; i < Avail_lits.size(); i++) {
    int lit = Avail_lits[i];
    if (Tried.find(lit) != Tried.end()) continue;    
    int var_ind = abs(lit)-1;

    if (max_lit == 0) { 
      max_lit = lit;
      max_act_var = Act0[var_ind] + Act1[var_ind];
      continue;
    }
    int val = Act0[var_ind] + Act1[var_ind];
    if (val > max_act_var) {
      max_act_var = val;
      max_lit = lit;
      count_eq = 0;
    }
    else if (val == max_act_var) count_eq++;
  }

 
  assert(max_lit != 0);
  B.push_back(max_lit);

} /* end of function act_var_init */

/*================================

  F I N D _ I N A C T  _ L I T

  ==============================*/
int CompInfo::find_inact_lit(CLAUSE &Curr,SCUBE &Tried,
                             FltCube &Act0,FltCube &Act1)
{

  float min_act_lit;
  int min_lit = 0;

  for (int i=0; i < Curr.size(); i++) {
    int lit = Curr[i];
    if (Tried.find(lit) != Tried.end()) continue;    
    int var_ind = abs(lit)-1;

    if (min_lit == 0) { 
      min_lit = lit;
      if (lit < 0) min_act_lit = Act0[var_ind];
      else min_act_lit = Act1[var_ind];
      continue;
    }

    if (lit < 0) {
      if (Act0[var_ind] < min_act_lit) {
	min_act_lit = Act0[var_ind];
	min_lit = lit; }}
    else 
      if (Act1[var_ind] < min_act_lit) {
	min_act_lit = Act1[var_ind];
	min_lit = lit;}
  }

  if (act_upd_mode == MINISAT_ACT_UPD)
    scale_factor_down(min_act_lit);

  assert(min_lit != 0);
  return(min_lit);
} /* end of function find_inact_lit */


/*================================

  F I N D _ I N A C T  _ V A R 

  ==============================*/
int CompInfo::find_inact_var(CLAUSE &Curr,SCUBE &Tried,FltCube &Act0,
                             FltCube &Act1)
{

  float min_var_act;
  int min_lit = 0;
  int count_eq = 0;

  for (int i=0; i < Curr.size(); i++) {
    int lit = Curr[i];
    if (Tried.find(lit) != Tried.end()) continue;    
    int var_ind = abs(lit)-1;

    if (min_lit == 0) { 
      min_lit = lit;
      min_var_act = Act0[var_ind] + Act1[var_ind];
      continue;
    }

    int val = Act0[var_ind]+Act1[var_ind];
    if (val < min_var_act) {
      min_var_act = val;
      min_lit = lit;
      count_eq = 0;
    }
    else if (val == min_var_act) count_eq++;
  }

  if (act_upd_mode == MINISAT_ACT_UPD)
    scale_factor_down(min_var_act);

  assert(min_lit != 0);
 
  return(min_lit);
} /* end of function find_inact_var */


/*========================================

  S C A L E _ F A C T O R _ D O W N

  =========================================*/
void CompInfo::scale_factor_down(float min_act)
{

  if (min_act < max_act_val) return;
 
  for (int i=0; i < max_pres_svar; i++) {
    Lit_act0[i] /= min_act;
    Lit_act1[i] /= min_act;
  }

  factor = 1.;

} /* end of function scale_factor_down */
