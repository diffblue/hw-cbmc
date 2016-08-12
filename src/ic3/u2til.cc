/******************************************************

Module:  Some auxiliary functions (Part 3)

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


/*=================================

  A D D _ F C L A U S E 2

  In contrast to 'add_fclause1'
  we assume that clause C is a 
  new one

  =================================*/
void CompInfo::add_fclause2(CLAUSE C,int last_ind,bool upd_activity)
{

  ClauseInfo el;
  int clause_ind = F.size();
  my_assert(C.size() > 0);

  sort(C.begin(),C.end());

 
  assert((last_ind >= 0) && (last_ind < Time_frames.size()));
  Time_frames[last_ind].num_bnd_cls++;

  
  el.span = last_ind;
  el.active = 1;
  el.skip = 0;
  el.delay = 0;

  Clause_info.push_back(el);
  
  Clause_table[C] = F.size();

  F.push_back(C);

  for (int i=1; i <= last_ind; i++) 
    Time_frames[i].Clauses.push_back(clause_ind);
  
  if (upd_activity) upd_act_lit_cnts(C,last_ind);

} /* end of function add_fclause2 */



/*===================================

  C L E A N _ C L A U S E _ S E T

  ====================================*/
void CompInfo::clean_clause_set()
{

  clean_formula();
  recomp_tf_cls_sets();
  build_new_clause_table();
  num_inact_cls = 0;

} /* end of function clean_clause_set */

/*============================================

  B U I L D _ N E W _ C L A U S E _ T A B L E 

  ===========================================*/
void CompInfo::build_new_clause_table()
{

  Clause_table.clear();

  for (int i=0; i < F.size(); i++) 
    Clause_table[F[i]] = i;
  

 // check that F does not have duplicate clauses
  assert(Clause_table.size() == F.size()); 

} /* end of function build_new_clause_table */


/*====================================

  C L E A N _ F O R M U L A

  ==================================*/
void CompInfo::clean_formula()
{

  int shift = 0;

  for (int i=0; i < F.size(); i++) {
    if (Clause_info[i].active == 0) {
      shift++;
      continue;
    }

    if (shift > 0)  {
      F[i-shift] = F[i];
      Clause_info[i-shift] = Clause_info[i];
    }
  }

  F.resize(F.size() - shift);
  Clause_info.resize(Clause_info.size() - shift);
} /* end of function clean_formula */


/*======================================

  R E C O M P _ T F _ C L S _ S E T S

  ======================================*/
void CompInfo::recomp_tf_cls_sets()
{

  for (int i=0; i < Time_frames.size(); i++) 
    Time_frames[i].Clauses.clear();

  assert(F.size() == Clause_info.size());

  for (int i=0; i < F.size(); i++) {   
    int span = Clause_info[i].span;
    for (int j=1; j <= span; j++) 
      Time_frames[j].Clauses.push_back(i);
  }

} /* end of function recomp_tf_cls_sets */


/*=====================================================

  U P D _ A C T _ L I T _ C N T S

  =====================================================*/
void CompInfo::upd_act_lit_cnts(CLAUSE &C,int last_ind)
{

  if (act_upd_mode == NO_ACT_UPD) return;

  float incr;


  if (act_upd_mode == TF_ACT_UPD) {
    incr = last_ind;
    //incr = 1;
  }
  else {
    assert(act_upd_mode == MINISAT_ACT_UPD);
    factor *= multiplier;   
    incr = factor;
  }

  
 
  for (int i=0; i < C.size(); i++) {
    int var_ind = abs(C[i])-1;
    if (C[i] < 0) Lit_act0[var_ind] += incr;
    else Lit_act1[var_ind] += incr;
  }
  

} /* end of function upd_act_lit_cnts */
