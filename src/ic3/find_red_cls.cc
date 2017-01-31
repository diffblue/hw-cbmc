/******************************************************

Module: Identifying redundant clauses 

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

/*===================================

  R E M _ R E D U N D _ C L A U S E S

  ====================================*/
int CompInfo::rem_redund_clauses()
{
 
  CUBE Old_nums;
  int count = 0;
  sort_in_length(Old_nums);
  form_lit_arrays(Old_nums);
 

  for (int i=0; i < Old_nums.size(); i++) {
    int clause_ind = Old_nums[i];
    if (Clause_info[clause_ind].active == 0) continue;
    CUBE Subsumed;
    check_for_subsumed_clauses1(Subsumed,clause_ind);
    count += Subsumed.size();
    for (int j=0; j < Subsumed.size(); j++) 
      remove_clause(Subsumed[j]);
  }

  return(count);
} /* end of function rem_redund_clauses */

/*============================================

  F O R M _ L I T _ A R R A Y S 

  ============================================*/
void CompInfo::form_lit_arrays(CUBE &Old_nums)
{

  for (int i=0; i < max_pres_svar; i++)  {
    Flits0[i].clear();
    Flits1[i].clear();
  }

  for (int i=Old_nums.size()-1; i>=0;i--) {
    int clause_ind = Old_nums[i];
    if (Clause_info[clause_ind].active == 0) continue;
    CLAUSE &C = F[clause_ind];
    for (int j=0; j < C.size(); j++) {
      int var_ind = abs(C[j])-1;
      if (C[j] < 0) Flits0[var_ind].push_back(clause_ind);
      else Flits1[var_ind].push_back(clause_ind);
    }
  }

} /* end of function form_lit_arrays */

/*===========================================

  S O R T _ I N _ L E N G T H

  ============================================*/
void CompInfo::sort_in_length(CUBE &Old_nums)
{

  // form pairs
  std::vector <LenInd> V;

  for (int i=0; i < F.size(); i++) {
    V.push_back(std::make_pair(F[i].size(),i));
  }

  sort(V.begin(),V.end(),compare_len());

  for (int i=0; i < V.size(); i++)
    Old_nums.push_back(V[i].second);

} /* end of function sort_in_length */



/*==========================================

  R E M O V E  _ C L A U S E

  ==========================================*/
void CompInfo::remove_clause(int clause_ind)
{
  
  Clause_info[clause_ind].active = 0;
  num_inact_cls++;
  int span = Clause_info[clause_ind].span;
  Time_frames[span].num_bnd_cls--;
  ClauseTable::iterator pnt = Clause_table.find(F[clause_ind]);
  assert(pnt != Clause_table.end());
  Clause_table.erase(pnt);
} /* end of function remove_clause */


/*=======================================================

  C H E C K _ F O R _ S U B S U M E D _ C L A U S E S 1

  =======================================================*/
void CompInfo::check_for_subsumed_clauses1(CUBE &Subsumed,int clause_ind0)
{


  CLAUSE &C = F[clause_ind0];
  int span0 = Clause_info[clause_ind0].span;
  int ind = find_best_ind2(C);

  CUBE *pClauses;

  int lit = C[ind];

  if (lit < 0) pClauses = &Flits0[-lit-1];
  else pClauses = &Flits1[lit-1];

  int len = C.size();
  for (int i=0; i < pClauses->size(); i++) {
    int clause_ind1 = (*pClauses)[i];
    if (Clause_info[clause_ind1].active == 0) continue;
    if (Clause_info[clause_ind1].span > span0) continue;
    if (F[clause_ind1].size() <= len) break;
    htable_lits.change_marker();
    htable_lits.started_using();
    mark_literals(htable_lits,F[clause_ind1]);
    if (subsumes(C,htable_lits))
      Subsumed.push_back(clause_ind1);
    htable_lits.done_using();
  }


} /* end of function check_for_subsumed_clauses1 */

/*======================================

  F I N D _ B E S T _ I N D 2

  =====================================*/
int CompInfo::find_best_ind2(CLAUSE &C)
{

  int min_size = F.size()+1;
  int min_ind = -1;


  for (int i=0; i < C.size(); i++) {
    int lit = C[i];
    int var_ind = abs(lit)-1;
    if (lit < 0) {
      if (Flits0[var_ind].size() < min_size) {
	min_size = Flits0[var_ind].size();
	min_ind = i;}
    }
    else // lit > 0
      if (Flits1[var_ind].size() < min_size) {
	min_size = Flits1[var_ind].size();
	min_ind = i;}
  }

  assert(min_ind >= 0);
  return(min_ind);

} /* end of function find_best_ind2 */

/*===================================

  M A R K _ L I T E R A L S

  ===================================*/
void CompInfo::mark_literals(hsh_tbl &Ht,CLAUSE &C)
{
  int marker = htable_lits.marker;
  CUBE &Table = htable_lits.Table;

  for (int i=0; i < C.size(); i++) {
    int var_ind = abs(C[i])-1;
    if (C[i] < 0) Table[var_ind] = marker;
    else Table[var_ind+max_num_vars] = marker;
  }
} /* end of function mark_literals */
