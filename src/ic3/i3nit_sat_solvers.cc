/******************************************************

Module: Initialization of Sat-solvers (Part 2)

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


/*========================================

  G E N _ U N I T _ C L A U S E S

  ========================================*/
void CompInfo::gen_unit_clauses(Minisat::SimpSolver *Sslvr,CNF &Uclauses)
{

  for (Minisat::TrailIterator pnt = Sslvr->trailBegin(); 
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
    if (Var_type[abs(C[i])-1] == INTERN) 
      return(false); // clause contains an internal variable

  return(true);

} /* end of function ext_clause */

/*==================================================

  A C C E P T _ S I M P L I F I E D _ F O R M

  =================================================*/
void CompInfo::accept_simplified_form(SatSolver &Slvr,
                                      Minisat::SimpSolver *Sslvr)
{

  Minisat::Solver *S = Slvr.Mst;
  for (Minisat::ClauseIterator pnt = Sslvr->clausesBegin(); 
       pnt != Sslvr->clausesEnd(); ++pnt) {
    const Minisat::Clause &M = *pnt;
    Minisat::vec<Minisat::Lit> C;
    for (int i = 0; i < M.size(); i++)
      C.push(M[i]);
    S->addClause(C);
  }

} /* end of function accept_simplified_form */
/*=======================================================

  C O P Y _  S I M P L I F I E D _ F O R M 

  ======================================================*/
void CompInfo::copy_simplified_form(Minisat::SimpSolver *Sslvr,
                                   CNF &Ext_clauses,CNF &Uclauses)
{

  assert(Simp_PrTr.size() == 0);
  for (Minisat::ClauseIterator pnt = Sslvr->clausesBegin(); 
       pnt != Sslvr->clausesEnd(); ++pnt) {
    const Minisat::Clause &M = *pnt;
    CLAUSE C;
    for (int i = 0; i < M.size(); i++)      {
      int lit = Minisat::var(M[i])+1;
      if (Minisat::sign(M[i])) lit = -lit;
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

  Minisat::SimpSolver *Sslvr = new Minisat::SimpSolver();

  for (int i = 0; i < max_num_vars0; i++) {
    Minisat::Var nv = Sslvr->newVar();    
  }

  // freeze variables
  for (int i=0; i < max_num_vars0; i++) 
    if (Var_type[i] != INTERN)
      Sslvr->setFrozen(i,true);

  CNF Ext_clauses;

  if (use_short_prop)  load_clauses(Ext_clauses,Sslvr,Short_prop);
  else load_clauses(Ext_clauses,Sslvr,Short_prop);

  load_clauses(Ext_clauses,Sslvr,Tr);

  // printf("Ext_clauses.size() = %d\n",Ext_clauses.size());
  // print_dnf(Ext_clauses);
  Sslvr->eliminate(true);

  CNF Uclauses;
  gen_unit_clauses(Sslvr,Uclauses);
  accept_simplified_form(Slvr,Sslvr);
  accept_new_clauses(Slvr,Ext_clauses);
  accept_new_clauses(Slvr,Uclauses);
  copy_simplified_form(Sslvr,Ext_clauses,Uclauses);
  delete Sslvr;  // delete this instance of SimpSolver
} /* end of function add_tf1_clauses */


/*==============================

    L O A D _ C L A U S E S 

  =============================*/
void CompInfo::load_clauses(CNF &Ext_clauses,Minisat::SimpSolver *Sslvr,CNF &A)
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
} /* end of function load_clauses */


/*=================================

  C O N V _ T O _ M C L A U S E

  ===============================*/
void CompInfo::conv_to_mclause(TrivMclause &A, CLAUSE &C) {

  for (int i=0; i < C.size(); i++) {
    if (C[i] > 0) A.push(Minisat::mkLit(C[i]-1,false));
    else A.push(Minisat::mkLit(-C[i]-1,true));

  }

} /* end of function conv_to_mclause */


/*======================================

  A D D _ T F 2 _ C L A U S E S

  =======================================*/
void CompInfo::add_tf2_clauses(SatSolver &Slvr)
{

  accept_new_clauses(Slvr,Simp_PrTr);

} /* end of function add_tf2_clauses */

