/******************************************************

Module: Generation of a counterexample

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

  F O R M _ I N P _ T R A C E

  ===========================================*/
void CompInfo::form_inp_trace(DNF &Inp_trace)
{

  assert(Obl_table.size() > 0);
  int succ_ind1 = Obl_table.size()-1;
  

  while (true) {
    Inp_trace.push_back(Obl_table[succ_ind1].Inp_assgn);
    succ_ind1 = Obl_table[succ_ind1].succ_ind;
    if (succ_ind1 < 0) return;
  }

} /* end of function form_inp_trace */

/*===========================================

  C H E C K _ O N E _ S T A T E _ C E X

  This function checks if the initial states
  are good

  ==========================================*/
bool CompInfo::check_one_state_cex()
{

  int num_vars = std::max(num_ist_vars,num_prop_vars);

  std::string Name = "Gen_sat";
  init_sat_solver(Gen_sat,num_vars,Name);

  // add formulas Ist
  accept_new_clauses(Gen_sat,Ist);

  // add Bad states

  add_bad_states(Gen_sat);


  bool sat_form = check_sat1(Gen_sat);
  bool ok = true;
  if (sat_form) {
    printf("an initial state does not satisfy the property\n");
    form_one_state_cex(Gen_sat);
    max_num_tfs = 0;
    ok = false;
  }

  delete_solver(Gen_sat);
  return(ok);

} /* end of function check_one_state_cex */

/*========================================

  C H E C K _ T W O _ S T A T E _ C E X

  =========================================*/
bool CompInfo::check_two_state_cex()
{


  std::string Name = "Gen_sat";
  init_sat_solver(Gen_sat,max_num_vars,Name);

  // add formulas Ist, Tr and Bad_states
  accept_new_clauses(Gen_sat,Ist);
  accept_new_clauses(Gen_sat,Tr);
  accept_new_clauses(Gen_sat,Bad_states);

  bool sat_form = check_sat1(Gen_sat);
  
  bool ok = true;
  if (sat_form) {
    form_two_state_cex(Gen_sat);
    max_num_tfs = 1;
    ok = false;
  }

  delete_solver(Gen_sat);
  return(ok);

} /* end of function check_two_state_cex */
  


/*=========================================

  F O R M _ T W O _ S T A T E _ C E X

  =========================================*/
void CompInfo::form_two_state_cex(SatSolver &Slvr)
{

  CUBE A,B;

  extr_cut_assgns1(A,Pres_svars,Slvr);
  Cex.push_back(A);

  A.clear();
  extr_cut_assgns1(B,Next_svars,Slvr);
  conv_to_pres_state(A,B);
  Cex.push_back(A);
  
} /* end of function form_two_state_cex */

/*=========================================

  F O R M _ O N E_ S T A T E _ C E X

  =========================================*/
void CompInfo::form_one_state_cex(SatSolver &Slvr)
{

  CUBE A;
  extr_cut_assgns1(A,Pres_svars,Slvr);
  Cex.push_back(A);

} /* end of function form_one_state_cex */

/*=====================================

  A D D _ N E G _ P R O P

  ====================================*/
void CompInfo::add_neg_prop(SatSolver &Slvr)
{
  for (int i=0; i < Prop.size()-1; i++) {
    accept_new_clause(Slvr,Prop[i]);
  }
  CLAUSE C = Prop.back();
  assert(C.size() == 1);
  C[0] = -C[0];
  accept_new_clause(Slvr,C);
} /* end of function add_neg_prop */

/*=====================================

  A D D _ B A D _ S T A T E S

  ====================================*/
void CompInfo::add_bad_states(SatSolver &Slvr)
{
  add_neg_prop(Slvr);

} /* end of function add_bad_states */
