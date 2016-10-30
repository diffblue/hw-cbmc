/******************************************************

Module: Initialization of Sat-solvers (Part 3)

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


/*==========================================

    F O R M _ S P E C _ S I M P _ P R _ T R

   This function is similiar to 
   'add_tf1_clauses'. The difference is that
   is uses Tr minus the clauses specifying
   'Constr_nilits'.

  ==========================================*/
void CompInfo::form_spec_simp_pr_tr(SatSolver &Slvr)
{

 Minisat::SimpSolver *Sslvr = new Minisat::SimpSolver();

  for (int i = 0; i < max_num_vars0; i++) {
    Minisat::Var nv = Sslvr->newVar();    
  }

  // freeze variables
  for (int i=0; i < max_num_vars0; i++) {
    if (Var_info[i].type == INTERN) 
      if (Var_info[i].value == 2) continue;
    
    Sslvr->setFrozen(i,true);
  }


  CNF Ext_clauses;

  if (use_short_prop)  load_clauses1(Ext_clauses,Sslvr,Short_prop);
  else load_clauses1(Ext_clauses,Sslvr,Short_prop);

  int num_clauses = Tr.size() - Constr_nilits.size();

  load_clauses2(Ext_clauses,Sslvr,Tr,num_clauses);


  Sslvr->eliminate(true);

  CNF Uclauses;
  gen_unit_clauses(Sslvr,Uclauses);
  accept_simplified_form(Slvr,Sslvr);
  accept_new_clauses(Slvr,Ext_clauses);
  accept_new_clauses(Slvr,Uclauses);
  
  delete Sslvr;  // delete this instance of SimpSolver


} /* end of function form_spec_simp_pr_tr */

/*==============================

    L O A D _ C L A U S E S 2

  =============================*/
void CompInfo::load_clauses2(CNF &Ext_clauses,Minisat::SimpSolver *Sslvr,
                             CNF &A,int num_clauses)
{
  for (int i=0; i < num_clauses; i++) {
    CLAUSE &C = A[i];
    if (ext_clause(C)) {
      Ext_clauses.push_back(C);
      continue;
    }

    TrivMclause M;
    conv_to_mclause(M,C);
    Sslvr->addClause(M);
  }
} /* end of function load_clauses2 */


/*===================================

  A D D _ C O N S T R _ N I L I T S

  =================================*/
void CompInfo::add_constr_nilits(CNF &Bad_states)
{

  SCUBE::iterator pnt;

  for (pnt = Constr_nilits.begin(); pnt != Constr_nilits.end(); pnt++) {
    int lit = *pnt;
    int var_ind = abs(lit)-1;
    if (Var_info[var_ind].type == NEXT_ST) continue;
    CLAUSE U;
    if (lit > 0) U.push_back(lit + max_num_vars0);
    else U.push_back(-(-lit + max_num_vars0));
    Bad_states.push_back(U);
  }

} /* end of function add_constr_nilits */
