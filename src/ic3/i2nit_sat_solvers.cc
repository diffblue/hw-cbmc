/******************************************************

Module: Initialization of Sat-solvers (Part 1)

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


/*======================================

  A D D _ T F 0 _ C L A U S E S

  =======================================*/
void CompInfo::add_tf0_clauses(SatSolver &Slvr)
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

  load_clauses(Ext_clauses,Sslvr,Tr);
  Sslvr->eliminate(true);

  accept_new_clauses(Slvr,Ist);
  accept_simplified_form(Slvr,Sslvr);
  accept_new_clauses(Slvr,Ext_clauses);
  delete Sslvr;  // delete this instance of SimpSolver

} /* end of function add_tf0_clauses */

/*=============================

  A S S G N _ V A R _ T Y P E

  ==============================*/
void CompInfo::assgn_var_type()
{

  Var_type.assign(max_num_vars,INTERN);

  SCUBE Pres_svars_set;
  SCUBE Next_svars_set;
  SCUBE Inp_vars_set;

  array_to_set(Pres_svars_set,Pres_svars);
  array_to_set(Next_svars_set,Next_svars);
  array_to_set(Inp_vars_set,Inp_vars);

  for (int i=0; i < Var_type.size(); i++) {

    if (Pres_svars_set.find(i+1) != Pres_svars_set.end()) {
      Var_type[i] = PRES_ST;
      continue;
    }

    if (Next_svars_set.find(i+1) != Next_svars_set.end()) {
      Var_type[i] = NEXT_ST;
      continue;
    }

    if (Inp_vars_set.find(i+1) != Inp_vars_set.end()) {
      Var_type[i] = INP;
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

  ======================================*/
void CompInfo::init_lbs_sat_solver()
{

  std::string Name = "Lbs_sat";
  init_sat_solver(Lbs_sat,max_num_vars0,Name);

  accept_new_clauses(Lbs_sat,Prop);

} /* end of function init_lbs_sat_solver */

/*========================================

  I N I T _ L G S  _ S A T _ S O L V E R

  ======================================*/
void CompInfo::init_lgs_sat_solver()
{

  std::string Name = "Lgs_sat";
  init_sat_solver(Lgs_sat,max_num_vars0,Name);
  assert(Simp_PrTr.size() > 0);
  accept_new_clauses(Lgs_sat,Simp_PrTr);
  

} /* end of function init_lgs_sat_solver */

/*========================================

  I N I T _ B S T _ S A T _ S O L V E R

  ======================================*/
void CompInfo::init_bst_sat_solver()
{
  std::string Name = "Bst_sat";
  init_sat_solver(Bst_sat,max_num_vars,Name);

  // accept property
  if (use_short_prop)  accept_new_clauses(Bst_sat,Short_prop);
  else accept_new_clauses(Bst_sat,Prop); 

  accept_new_clauses(Bst_sat,Tr); // accept transition relation
//accept negation of property (bad states)                                         
  accept_new_clauses(Bst_sat,Bad_states); 

  CUBE &Clauses = Time_frames[tf_lind].Clauses;
  for (int i=0; i < Clauses.size();i++) {
    int clause_ind = Clauses[i];
    accept_new_clause(Bst_sat,F[clause_ind]);
  }
} /* end of function init_bst_sat_solver */

