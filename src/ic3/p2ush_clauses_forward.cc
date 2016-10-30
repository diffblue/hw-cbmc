/******************************************************

Module: Pushing clauses to later time frames (Part 1)

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

/*===========================================

  P U S H _ C L A U S E S _ F O R W A R D

  ===========================================*/
void CompInfo::push_clauses_forward()
{
  if (verbose == 0) {
    printf("%*c",3,' ');
    printf("push_clauses_forward\n");  
  }

  int min_tf = 1;
 
  assert(tf_lind < Time_frames.size());
  init_fields();
  for (int i=min_tf; i <= tf_lind; i++) { 
    CUBE Pushed;
    CUBE &Clauses = Time_frames[i].Clauses;
    for (int j=0; j  < Clauses.size();j++) { 
      int clause_ind = Clauses[j];
      if (Clause_info[clause_ind].active == 0) continue;
      if (Clause_info[clause_ind].skip) continue;
      if (Clause_info[clause_ind].span != i) continue;    

      CLAUSE C;
     
      bool ok = push_clause(C,i,clause_ind);
      if (!ok) {
	Clause_info[clause_ind].skip = 1;
	continue;
      }

     
      if (F[clause_ind].size() > C.size()) {	 
	int ans = replace_or_add_clause(clause_ind,C,i);
	if (ans == RESTORE) {
	  C = F[clause_ind];
	  Clause_info[clause_ind].delay = 1;
	}
	else if (ans == REPLACED) {
	  add_copies(i,C);
	}
	else if (ans == ADD1) {
	  add_fclause1(C,i+1,PUSH_STATE);
	  continue;
	}
	else if (ans == ADD2) {	 
	  add_fclause2(C,i+1,true);
	  add_copies(i,C);
	  continue;}
      }
      else  // C.size() == F[clause_ind.size()
	if (Clause_info[clause_ind].span < i) {
	  Clause_info[clause_ind].delay = 1;
	  continue;
	}

   
   
      if (Clause_info[clause_ind].span == i) {
	Pushed.push_back(clause_ind);
	Clause_info[clause_ind].span++;
	Time_frames[i].num_bnd_cls--;
	Time_frames[i+1].num_bnd_cls++;
	Time_frames[i+1].Clauses.push_back(clause_ind);
      }
     
     
    } /* for j */
    

    add_new_clauses(Time_frames[i+1].Slvr,Pushed);

    if (Time_frames[i].num_bnd_cls == 0) {
      inv_ind = i;
      printf("All clauses of Bnd[%d] are pushed forward\n",inv_ind);
      break;}
   
  }
 
} /* end of function push_clauses_forward */


/*=============================

  P U S H _ C L A U S E

  returns 'true' if formula
  is unsatisfiable

  ============================*/
bool CompInfo::push_clause(CLAUSE &C,int tf_ind,int clause_ind) 
{
  num_push_clause_calls++;
  SatSolver &Slvr = Time_frames[tf_ind].Slvr;
 
  
  MvecLits Assmps;
  add_negated_assumps2(Assmps,F[clause_ind],true);
  
  
  // run a SAT-check
  
  bool sat_form = check_sat2(Slvr,Assmps);
 
  if (sat_form) {
    return(false);
  }

  
  CLAUSE C0;
  gen_assump_clause(C0,Slvr,Assmps);
  conv_to_pres_state(C,C0);
  if (!corr_clause(C)) modif_ind_clause(C,F[clause_ind]);  
  return(true);
} /* end of function push_clause */


/*===============================================

  R E P L A C E _ O R _ A D D _ C L A U S E

  ASSUMPTIONS:

  1) C strictly subsumes F[clause_ind]

  2) Set 'Bnd' that contains F[clause_ind]
  does not contain clause C

  ==============================================*/
int CompInfo::replace_or_add_clause(int clause_ind,CLAUSE &C,int tf_ind)
{
 
  sort(C.begin(),C.end());
  ClauseTable::iterator pnt1 = Clause_table.find(C);
  ClauseTable::iterator pnt2 = Clause_table.find(F[clause_ind]);


  int clause_ind1 = -1;
  int span1 = -1;
  int span = Clause_info[clause_ind].span;

  if (pnt1 != Clause_table.end())  {
    clause_ind1 = Clause_table[C];
    span1 = Clause_info[clause_ind1].span;
    if (span1 > span) {
      num_restore_cases++;
      return(RESTORE);
    }
  }
  
  if (tf_ind < span)
    if (clause_ind == -1) { // C is a new clause
      num_add2_cases++;
      return(ADD2);  
    }
    else // C exists
      if (span1 <= tf_ind) { // push forward an existing clause
	num_add1_cases++;
	return(ADD1);}
      else if (span1 < span) { // pushing forward does not make sense 
	num_restore_cases++; // and replacement is incorrect
	return(RESTORE);
      }

  assert(pnt2 != Clause_table.end());
 
  Clause_table.erase(pnt2);
 
  F[clause_ind] = C;

  if (clause_ind1 == -1) {
    Clause_table[C] = clause_ind;   
    num_replaced_cases++;
    return(REPLACED);
  }


  assert(clause_ind1 >= 0);
  assert(clause_ind1 < F.size());


  Clause_info[clause_ind1].active = 0;
  num_inact_cls++;
  
  assert(span1 <= Clause_info[clause_ind].span);

  Time_frames[span1].num_bnd_cls--;
  
  Clause_table[C] = clause_ind;
  num_replaced_cases++;
  return(REPLACED);

} /* end of function replace_or_add_clause */
