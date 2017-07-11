/******************************************************

Module: Verification of a counterexample/invariant 
        (Part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"
/*================================

  V E R _ T R A N S _ I N V

  =================================*/
bool CompInfo::ver_trans_inv()
{

  CNF H;
  assert(Time_frames[inv_ind].num_bnd_cls == 0);
  CUBE Old_nums;
  gen_form2(H,Old_nums,inv_ind+1);
  bool ok = ver_ini_states(H);
  if (!ok) return(false);
  ok = ver_invar(H,Old_nums);
  if (!ok) return(false);
  M->result() << "inductive invariant verification is ok" << M->eom;
  return(true);
} /* end of function ver_trans_inv */

/*==========================

  V E R _ I N V A R

  =========================*/
bool CompInfo::ver_invar(CNF &H,CUBE &Old_nums)
{

  std::string Name("Gen_sat");
  init_sat_solver(Gen_sat,max_num_vars,Name);

  // add property
  if (use_short_prop)  accept_new_clauses(Gen_sat,Short_prop);
  else accept_new_clauses(Gen_sat,Prop);


  accept_new_clauses(Gen_sat,H);
  accept_new_clauses(Gen_sat,Tr);

  for (size_t i=0; i < Bad_states.size(); i++) 
    accept_new_clause(Gen_sat,Bad_states[i]);

  bool sat_form = check_sat1(Gen_sat);
  if (sat_form) {
    M->error() << "bad state is reachable: ";
    CUBE St,Nst,Pst;
    extr_cut_assgns1(Nst,Next_svars,Gen_sat);
    conv_to_pres_state(St,Nst);
    M->error() << ivect_to_str(St) << M->eom;
    return(false);
  }
  

  bool ok = ver_ind_clauses2(H,Old_nums);
  delete_solver(Gen_sat);
  return(ok);

} /* end function ver_invar */


/*=====================================

  V E R _ I N D _ C L A U S E S 2

  ======================================*/
bool CompInfo::ver_ind_clauses2(CNF &H,CUBE &Old_nums)
{
 
  for (size_t i=0; i < H.size(); i++) {
    CLAUSE C;
    conv_to_next_state(C,H[i]);
    MvecLits Assmps;
    add_negated_assumps1(Assmps,C);   
    bool sat_form = check_sat2(Gen_sat,Assmps);
    if (sat_form) {
      M->error() << "inductive invariant verification failed" << M->eom;
      M->error() << "Inv & T does not imply F'[" << Old_nums[i] << "]"
		 << M->eom;
      M->error() << "F[" << Old_nums[i] << "]-> "; 
      M->error() << H[i] << M->eom;
      M->error() << "F'[" << Old_nums[i] << "]-> ";
      M->error() << C << M->eom;
      CUBE St0,St1;
      print_bnd_sets1(messaget::M_ERROR);    
      return(false);
    }
  }
   
  return(true);
} /* end of function ver_ind_clauses2 */

/*=============================

      G E N _ F O R M 1

  ==============================*/
void CompInfo::gen_form1(CNF &H,int k) 
{
  assert(k >= 0);
 
  for (size_t i=0; i < F.size(); i++) {
    if (Clause_info[i].active == 0) continue;
    if (Clause_info[i].span < (size_t) k) continue;
    H.push_back(F[i]);
  }

} /* end of function gen_form1 */


/*============================

  V E R _ P R O P

  Returns 'true' if all initial
  states are good

  ===========================*/
bool CompInfo::ver_prop()
{

  add_neg_prop(Gen_sat);

  bool sat_form = check_sat1(Gen_sat);
  if (sat_form) {
    M->error() << "inductive invariant verification failed" << M->eom;
    M->error() << "Ist does not imply Prop" << M->eom;
    return(false);
  }

  return(true);

} /* end of function ver_prop */

/*==============================

  V E R _ I N I _ S T A T E S

  ===============================*/
bool CompInfo::ver_ini_states(CNF &H)
{

  std::string Name("Gen_sat");
  init_sat_solver(Gen_sat,max_num_vars,Name);
  
  accept_new_clauses(Gen_sat,Ist);  

  accept_constrs(Gen_sat);
  bool ok = ver_prop();
  if (!ok) return(false);

  ok = ver_ind_clauses1(H);
  delete_solver(Gen_sat);
  return(ok);

} /* end of function ver_ini_states */


/*======================================

  F I N D _ W R O N G _ T R A N S I T I O N

  =======================================*/
void CompInfo::find_wrong_transition(CUBE &St0,CUBE &St1,SatSolver &Slvr)
{

  extr_cut_assgns1(St0,Pres_svars,Slvr);
  CUBE St;
  extr_cut_assgns1(St,Next_svars,Slvr);
  conv_to_pres_state(St1,St);

} /* end of function find_wrong_transition */


/*===================================

  V E R _ I N D _ C L A U S E S 1

  ====================================*/
bool CompInfo::ver_ind_clauses1(CNF &H)
{
 
  for (size_t i=0; i < H.size(); i++) {

    MvecLits Assmps;
    add_negated_assumps1(Assmps,H[i]);
   
    bool sat_form = check_sat2(Gen_sat,Assmps);
    if (sat_form) {
      M->error() << "inductive invariant verification failed" << M->eom;
      M->error() << "clause F[" << i << "] excludes an initial state: ";
      M->error() << ivect_to_str(H[i]) << M->eom;
      return(false);
    }
  }
   
  return(true);
} /* end of function ver_ind_clauses1 */
