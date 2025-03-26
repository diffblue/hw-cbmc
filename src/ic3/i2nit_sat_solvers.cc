/******************************************************

Module: Initialization of Sat-solvers (Part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <util/invariant.h>
#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

/*======================================

      A D D _ T F 0 _ C L A U S E S

  =======================================*/
void CompInfo::add_tf0_clauses(SatSolver &Slvr)
{

  IctMinisat::SimpSolver *Sslvr = new IctMinisat::SimpSolver();

  for (size_t i = 0; i < max_num_vars0; i++) {
    UNUSED IctMinisat::Var nv = Sslvr->newVar();
  }

  
  // freeze variables
  for (size_t i=0; i < max_num_vars0; i++) {
    if (Var_info[i].type == INTERN) 
      if (Var_info[i].value == 2) continue;
    
    Sslvr->setFrozen(i,true);
  }

  CNF Ext_clauses;

  load_clauses1(Ext_clauses,Sslvr,Tr);
  Sslvr->eliminate(true);

  accept_new_clauses(Slvr,Ist);
  accept_simplified_form(Slvr,Sslvr);
  accept_new_clauses(Slvr,Ext_clauses);
  delete Sslvr;  // delete this instance of SimpSolver

} /* end of function add_tf0_clauses */

/*=============================

   A S S I G N _ V A R _ T Y P E

  ==============================*/
void CompInfo::assign_var_type()
{

  VarInfo el;
  el.type = INTERN;
  el.value = 2;
  Var_info.assign(max_num_vars,el);

  SCUBE Pres_svars_set;
  SCUBE Next_svars_set;
  SCUBE Inp_vars_set;

  array_to_set(Pres_svars_set,Pres_svars);
  array_to_set(Next_svars_set,Next_svars);
  array_to_set(Inp_vars_set,Inp_vars);

  for (size_t i=0; i < Var_info.size(); i++) {

    if (Pres_svars_set.find(i+1) != Pres_svars_set.end()) {
      Var_info[i].type = PRES_ST;
      continue;
    }

    if (Next_svars_set.find(i+1) != Next_svars_set.end()) {
      Var_info[i].type = NEXT_ST;
      continue;
    }

    if (Inp_vars_set.find(i+1) != Inp_vars_set.end()) {
      Var_info[i].type = INP;
      continue;
    }

  }

} /* end of function assgn_var_type */

/*=============================================

  I N I T _ T I M E _ F R A M E _ S O L V E R

  ============================================*/
void CompInfo::init_time_frame_solver(int tf_ind)
{
 
  SatSolver &Slvr = Time_frames[tf_ind].Slvr;
  char Name[MAX_NAME];
  sprintf(Name,"Tf_sat%d",tf_ind);
  std::string Slv_name = Name;
  init_sat_solver(Slvr,max_num_vars0,Slv_name);
  
  if (tf_ind == 0) add_tf0_clauses(Slvr);
  else if (tf_ind == 1) add_tf1_clauses(Slvr);
  else add_tf2_clauses(Slvr);

} /* end of function init_time_frame_solver */

/*========================================

  I N I T _ L B S  _ S A T _ S O L V E R

  ASSUMPTIONS:

   1) The last clause of 'Prop' is unit.
      It forces the property the propery
      output to 1

  ======================================*/
void CompInfo::init_lbs_sat_solver()
{

  std::string Name = "Lbs_sat";
  init_sat_solver(Lbs_sat,max_num_vars0,Name);

  for (size_t i=0; i < Prop.size()-1; i++) 
    accept_new_clause(Lbs_sat,Prop[i]);

  CLAUSE U = Prop.back();
  assert(U.size() == 1);


 // add literals constraining internal variables

  for (size_t i=0; i < Fun_coi_lits.size(); i++) {
    int lit = Fun_coi_lits[i];
    int var_ind = abs(lit)-1;
    INVARIANT(Var_info[var_ind].type == INTERN,
              "Type of literal should be INTERN");
    U.push_back(-lit);
  }

  accept_new_clause(Lbs_sat,U);

  // add constraints on comb. input and pres. state
  // variables

 for (size_t i=0; i < Constr_ilits.size(); i++) {
    CLAUSE U1;
    U1.push_back(Constr_ilits[i]);
    accept_new_clause(Lbs_sat,U1);
  }

} /* end of function init_lbs_sat_solver */

/*========================================

  I N I T _ L G S  _ S A T _ S O L V E R

  ======================================*/
void CompInfo::init_lgs_sat_solver()
{

  std::string Name = "Lgs_sat";
  init_sat_solver(Lgs_sat,max_num_vars0,Name);
  assert(Simp_PrTr.size() > 0);

  if (Constr_nilits.size() == 0) {
    accept_new_clauses(Lgs_sat,Simp_PrTr);
    return;}

 
  form_spec_simp_pr_tr(Lgs_sat);
 

} /* end of function init_lgs_sat_solver */

/*========================================

  I N I T _ B S T _ S A T _ S O L V E R

  ======================================*/
void CompInfo::init_bst_sat_solver()
{
  std::string Name = "Bst_sat";
  init_sat_solver(Bst_sat,max_num_vars,Name);

  // accept property and transition relation

  if (use_short_prop)  accept_new_clauses(Bst_sat,Short_prop);
  else accept_new_clauses(Bst_sat,Prop); 

  accept_new_clauses(Bst_sat,Tr); 
 
  accept_new_clauses(Bst_sat,Bad_states); // accept negation of property 
  
  CUBE &Clauses = Time_frames[tf_lind].Clauses;
  for (size_t i=0; i < Clauses.size();i++) {
    int clause_ind = Clauses[i];
    accept_new_clause(Bst_sat,F[clause_ind]);
  }
} /* end of function init_bst_sat_solver */






