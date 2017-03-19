/******************************************************

Module: Initialization of Sat-solvers (Part 2)

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


/*========================================

  G E N _ U N I T _ C L A U S E S

  ========================================*/
void CompInfo::gen_unit_clauses(IctMinisat::SimpSolver *Sslvr,CNF &Uclauses)
{

  for (IctMinisat::TrailIterator pnt = Sslvr->trailBegin(); 
       pnt != Sslvr->trailEnd(); ++pnt) {
    int lit = mlit_to_lit(Sslvr,*pnt);
    CLAUSE U;
    U.push_back(lit);
    Uclauses.push_back(U);
  }
 

} /* end of function print_sslvr_assgns */

/*==============================

  E X T _ C L A U S E

  Returns 'true' if C consists
  only of external variables

  =============================*/
bool CompInfo::ext_clause(CLAUSE &C)
{

  for (int i=0; i < C.size(); i++) 
    if (Var_info[abs(C[i])-1].type == INTERN) 
      return(false); // clause contains an internal variable

  return(true);

} /* end of function ext_clause */

/*==================================================

  A C C E P T _ S I M P L I F I E D _ F O R M

  =================================================*/
void CompInfo::accept_simplified_form(SatSolver &Slvr,
                                      IctMinisat::SimpSolver *Sslvr)
{

  IctMinisat::Solver *S = Slvr.Mst;
  for (IctMinisat::ClauseIterator pnt = Sslvr->clausesBegin(); 
       pnt != Sslvr->clausesEnd(); ++pnt) {
    const IctMinisat::Clause &M = *pnt;
    IctMinisat::vec<IctMinisat::Lit> C;
    for (int i = 0; i < M.size(); i++)
      C.push(M[i]);
    S->addClause(C);
  }

} /* end of function accept_simplified_form */
/*==================================================

     C O P Y _  S I M P L I F I E D _ F O R M 

  ================================================*/
void CompInfo::copy_simplified_form(IctMinisat::SimpSolver *Sslvr,
                                   CNF &Ext_clauses,CNF &Uclauses)
{

  assert(Simp_PrTr.size() == 0);
  for (IctMinisat::ClauseIterator pnt = Sslvr->clausesBegin(); 
       pnt != Sslvr->clausesEnd(); ++pnt) {
    const IctMinisat::Clause &M = *pnt;
    CLAUSE C;
    for (int i = 0; i < M.size(); i++)      {
      int lit = IctMinisat::var(M[i])+1;
      if (IctMinisat::sign(M[i])) lit = -lit;
      C.push_back(lit);
    }
    Simp_PrTr.push_back(C);
  }

  for (int i=0; i < Ext_clauses.size(); i++)
    Simp_PrTr.push_back(Ext_clauses[i]);

  for (int i=0; i < Uclauses.size(); i++)
    Simp_PrTr.push_back(Uclauses[i]);

} /* end of function copy_simplified_form */



/*======================================

     A D D _ T F 1 _ C L A U S E S

  =======================================*/
void CompInfo::add_tf1_clauses(SatSolver &Slvr)
{

  IctMinisat::SimpSolver *Sslvr = new IctMinisat::SimpSolver();

  for (int i = 0; i < max_num_vars0; i++) {
    IctMinisat::Var nv = Sslvr->newVar();    
  }

  // freeze variables
  for (int i=0; i < max_num_vars0; i++) {
    if (Var_info[i].type == INTERN) 
      if (Var_info[i].value == 2) continue;
    
    Sslvr->setFrozen(i,true);
  }


  CNF Ext_clauses;

  if (use_short_prop)  load_clauses1(Ext_clauses,Sslvr,Short_prop);
  else load_clauses1(Ext_clauses,Sslvr,Prop);

  load_clauses1(Ext_clauses,Sslvr,Tr);

  Sslvr->eliminate(true);

  CNF Uclauses;
  gen_unit_clauses(Sslvr,Uclauses);
  accept_simplified_form(Slvr,Sslvr);
  accept_new_clauses(Slvr,Ext_clauses);
  accept_new_clauses(Slvr,Uclauses);
  copy_simplified_form(Sslvr,Ext_clauses,Uclauses);
  delete Sslvr;  
} /* end of function add_tf1_clauses */


/*==============================

    L O A D _ C L A U S E S 1

  =============================*/
void CompInfo::load_clauses1(CNF &Ext_clauses,IctMinisat::SimpSolver *Sslvr,CNF &A)
{
  for (int i=0; i < A.size(); i++) {
    CLAUSE &C = A[i];
    if (ext_clause(C)) {
      Ext_clauses.push_back(C);
      continue;
    }

    TrivMclause M;
    conv_to_mclause(M,C);
    Sslvr->addClause(M);
  }
} /* end of function load_clauses1 */


/*=================================

  C O N V _ T O _ M C L A U S E

  ===============================*/
void CompInfo::conv_to_mclause(TrivMclause &A, CLAUSE &C) {

  for (int i=0; i < C.size(); i++) {
    if (C[i] > 0) A.push(IctMinisat::mkLit(C[i]-1,false));
    else A.push(IctMinisat::mkLit(-C[i]-1,true));

  }

} /* end of function conv_to_mclause */


/*======================================

  A D D _ T F 2 _ C L A U S E S

  =======================================*/
void CompInfo::add_tf2_clauses(SatSolver &Slvr)
{

  accept_new_clauses(Slvr,Simp_PrTr);

} /* end of function add_tf2_clauses */

