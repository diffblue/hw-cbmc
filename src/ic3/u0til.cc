/******************************************************

Module:  Some auxiliary functions (Part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>
#include <sys/resource.h>


#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"




/*==========================================

  A C C E P T _ N E W _ C L A U S E S

  =========================================*/
void CompInfo::accept_new_clauses(SatSolver &Slvr,DNF &H)
{
  for (size_t i=0; i < H.size(); i++)
    accept_new_clause(Slvr,H[i]);

} /* end of function accept_new_clauses */

/*=======================================

  A C C E P T _ N E W _ C L A U S E

  ========================================*/
void CompInfo::accept_new_clause(SatSolver &Slvr,CLAUSE &C)
{

  assert(C.size() > 0);
 

  TrivMclause A;
  conv_to_mclause(A,C);
  Slvr.Mst->addClause(A);


}  /* end of function accept_new_clause */

/*==========================================================

  G E T _ R U N T I M E

  the function compute the sytem and user time spent by the 
  process
  
  ============================================================*/
void get_runtime (double &usrtime, double &systime)
{
  struct rusage timeusage;

  getrusage(RUSAGE_SELF, &timeusage);

  usrtime = (double)timeusage.ru_utime.tv_sec  + 
    (double)timeusage.ru_utime.tv_usec / 1000000;
  systime = (double)timeusage.ru_stime.tv_sec  + 
    (double)timeusage.ru_stime.tv_usec / 1000000;
} /* end of function get_runtime */


/*=======================================

  P A R T _ S O R T

  ========================================*/
void CompInfo::part_sort(CLAUSE &C1,CLAUSE &C, std::vector <ActInd> &V) {

  
  CCUBE Marked;
  Marked.assign(C.size(),0);


  size_t min_size0 = (max_num_elems < C.size())? max_num_elems : C.size();

  size_t min_size = min_size0;
  for (size_t i=0; i < min_size0; i++) 
    if (V[i].first < 0.1) {
      min_size = i;
      break;
    }

  for (size_t i=0; i < min_size; i++) {
    int old_ind = V[i].second;
    C1.push_back(C[old_ind]);
    Marked[old_ind] = 1;
   
  }
 
  for (size_t i=0; i < C.size(); i++) {
    if (Marked[i]) continue;
    C1.push_back(C[i]);
  }

  if (C.size() != C1.size()) {
    p();
    M->error() << "C.size() = " << C.size() << ", C1.size() = " <<  C1.size()
	       << M->eom;
    throw(ERROR1);
  }
  
} /* end of function part_sort */

/*============================================

  A D D _ T E M P _ C L A U S E

  ===========================================*/
void CompInfo::add_temp_clause(Mlit &act_lit,SatSolver &Slvr,CLAUSE &C)
{

  act_lit = IctMinisat::mkLit(Slvr.Mst->newVar(),false);
  TrivMclause A;
  conv_to_mclause(A,C);
  A.push(~act_lit);
  Slvr.Mst->addClause(A);

} /* end of function add_temp_clause */

/*===================================

  A R R A Y _ T O _ S E T

  ==================================*/
void array_to_set(SCUBE &A,CUBE &B)
{
  for (size_t i=0; i < B.size(); i++)
    A.insert(B[i]);

} /* end of function array_to_set */


/*==================================

  P R I N T _ B N D _ S E T S 1

  ===================================*/
void CompInfo::print_bnd_sets1(unsigned message_level)
{

  messaget::mstreamt &Ms = M->get_mstream(message_level);
  for (size_t i=0; i < Time_frames.size(); i++) {
    Ms << "Bnd[" << i << "]: ";
    int count = 0;
    for (size_t j=0; j < F.size(); j++) {
      if (Clause_info[j].active == 0) continue;
      if (Clause_info[j].span != i) continue;
      if (count++ > 0) Ms << " ";
      Ms << j;
    }
    Ms << M->eom;
  }
} /* end of function print_bnd_sets1 */

/*==============================================

  E X T R _ C U T _ A S S G N S 1

  ASSUMPTIONS:
  1) Vars contains variables

  ===============================================*/
void CompInfo::extr_cut_assgns1(CUBE &Assgns,CUBE &Vars,SatSolver &Slvr)
{

  MboolVec &S = Slvr.Mst->model;
  for (size_t i=0; i < Vars.size(); i++) {
    int var_ind = Vars[i]-1;
    if (S[var_ind] == Mtrue) Assgns.push_back(var_ind+1);
    else Assgns.push_back(-(var_ind+1));
  }

} /* end of function extr_cut_assgns1 */

/*==============================================

  E X T R _ C U T _ A S S G N S 2

  ASSUMPTIONS:
  1) Lits contains literals rather than variables

  ===============================================*/
void CompInfo::extr_cut_assgns2(CUBE &Assgns,CUBE &Lits,SatSolver &Slvr)
{

  MboolVec &S = Slvr.Mst->model;
  for (size_t i=0; i < Lits.size(); i++) {
    int var_ind = abs(Lits[i])-1;
    if (S[var_ind] == Mtrue) Assgns.push_back(var_ind+1);
    else Assgns.push_back(-(var_ind+1));
  }

} /* end of function extr_cut_assgns2 */
