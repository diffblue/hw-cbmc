/******************************************************

Module: Verification of a counterexample/invariant 
        (Part 2)

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


/*====================================

       G E N _ F O R M 2

   In contrast to 'gen_form1' this
   function returns array 'Old_nums'
   specifying the indexes of clauses
   of H in F.

  ===================================*/
void CompInfo::gen_form2(CNF &H,CUBE &Old_nums,int k) 
{
  assert(k >= 0);
 
  for (size_t i=0; i < F.size(); i++) {
    if (Clause_info[i].active == 0) continue;
    if (Clause_info[i].span < (size_t) k) continue;
    H.push_back(F[i]);
    Old_nums.push_back(i);
  }

} /* end of function gen_form2 */



/*=========================

      V E R _ C E X

  ========================*/
bool CompInfo::ver_cex()
{

  assert(Cex.size() > 0);

  bool ok = check_init_state(Cex[0]);
  M->result() << "Cex.size() = " << Cex.size() << M->eom;
  if (!ok) return(false);

  std::string Name = "Gen_sat";
  if (Cex.size() == 1) goto FINISH;
  
  init_sat_solver(Gen_sat,max_num_vars,Name);
  accept_new_clauses(Gen_sat,Tr);

  for (size_t i=0; i < Cex.size()-1; i++) {
    bool ok = check_transition(Cex[i],Cex[i+1]);
    if (!ok) {
      M->error() << "verfication failed" << M->eom;
      M->error() << "wrong transition S" << i << "-> S" << i+1 << M->eom;
      return(false);
    }
  }

  delete_solver(Gen_sat);

  ok = check_bad_state(Cex.back());
  if (!ok) return(false);

 FINISH:
  M->result() << "cex verification is ok" << M->eom;
  return(true);
} /* end of function ver_cex */


/*=====================================

     C H E C K _ B A D _ S T A T E

  =====================================*/
bool CompInfo::check_bad_state(CUBE &St)
{

  std::string Name = "Gen_sat";
  init_sat_solver(Gen_sat,max_num_vars,Name);
  add_neg_prop(Gen_sat);
  add_constr_lits2(Gen_sat);
  MvecLits Assmps;
  add_assumps1(Assmps,St);
  bool sat_form = check_sat2(Gen_sat,Assmps);
  if (sat_form == false) {
    M->error() << "cex verification failed" << M->eom;
    M->error() << "last state of Cex is a good one" << M->eom;
    M->error() << "St-> " << ivect_to_str(St) << M->eom;;
    M->error() << "sat_form = " << sat_form << M->eom;
    return(false); }

  delete_solver(Gen_sat);
  return(true);
} /* end of function check_bad_state */


/*==========================================

       C H E C K _ T R A N S I T I O N

 ==========================================*/
bool CompInfo::check_transition(CUBE &St0,CUBE &St1)
{

  MvecLits Assmps;
  add_assumps1(Assmps,St0);

  CUBE Nst1;
  conv_to_next_state(Nst1,St1);
  add_assumps1(Assmps,Nst1);
  bool ok = true;
  bool sat_form = check_sat2(Gen_sat,Assmps);
  if (sat_form == false) ok = false;
  return(ok);


} /* end of function check_transition */

/*=======================================

      C H E C K _ I N I T _ S T A T E

  ========================================*/
bool CompInfo::check_init_state(CUBE &St)
{

  std::string Name = "Gen_sat";
  init_sat_solver(Gen_sat,max_num_vars,Name);

  accept_new_clauses(Gen_sat,Ist);

  MvecLits Assmps;
  add_assumps1(Assmps,St);
  
  bool sat_form = check_sat2(Gen_sat,Assmps);
  if (sat_form == false) {
    M->error() << "cex verification failed" << M->eom;
    M->error() << "Cex starts with a non-initial state" << M->eom;
    return(false);
  }

  delete_solver(Gen_sat);
  return(true);

} /* end of function check_init_state */



/*======================================

     A D D _ C O N S T R _ L I T S 2 

  =====================================*/
void CompInfo::add_constr_lits2(SatSolver &Slvr)
{

  for (size_t i=0; i < Constr_ilits.size(); i++) {
    CLAUSE U;
    U.push_back(Constr_ilits[i]);
    accept_new_clause(Slvr,U);
  }

  SCUBE::iterator pnt;
  for (pnt = Constr_nilits.begin(); pnt != Constr_nilits.end(); pnt++) {
    CLAUSE U;
    U.push_back(*pnt);
    accept_new_clause(Slvr,U);
  }

} /* end of function add_constr_lits2 */
