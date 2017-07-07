/******************************************************

Module: Initialization of IC3

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
/*==============================

    C I _ I N I T

  ===============================*/
void CompInfo::ci_init()
{

  add_time_frame();
  add_time_frame();
 
  assert(max_pres_svar > 0);
  Lit_act0.assign(max_pres_svar,0.);
  Lit_act1.assign(max_pres_svar,0.);
  Tmp_act0.assign(max_pres_svar,0);
  Tmp_act1.assign(max_pres_svar,0);

  for (size_t i=0; i < Ist.size(); i++) 
    add_fclause2(Ist[i],0,false);
 

  inv_ind = -1;
  orig_ind_cls = 0;
  succ_impr = 0;
  failed_impr = 0;
  max_num_impr = 0;
  num_inact_cls = 0;
  num_add1_cases = 0;
  num_add2_cases = 0;
  num_restore_cases = 0;
  num_replaced_cases = 0;
 

  for (int i=0; i < max_pres_svar; i++) {
    CUBE Dummy;
    Flits0.push_back(Dummy);
    Flits1.push_back(Dummy);
  }

  num_push_clause_calls = 0;
  num_bstate_cubes = 0; 
  length_bstate_cubes = 0.;  
  num_gstate_cubes = 0; 
  length_gstate_cubes = 0.; 
  old_state_cnt = 0;
  triv_old_st_cnt = 0;
  new_state_cnt = 0;
  root_state_cnt = 0;
  tot_ctg_cnt = 0;
  succ_ctg_cnt = 0;
  vac_true = false;
 
} /* end of function ci_init */

/*=============================================

   F O R M _ S H O R T _ P R O P E R T Y

   Does to 'Short_pop' what 'form_property'
   does to 'Prop'.
 
   Uses the same assumptions as 
   'form_property'

  ============================================*/
void CompInfo::form_short_property()
{
  CLAUSE &C = Short_prop.back();
  assert(C.size() == 1);
  C[0] = -C[0];

} /* end of function form_short_property */

/*==================================

     F O R M _ P R O P E R T Y


 ASSUMPTIONS:
   1) Currently 'Prop' specifies the
      bad states in terms of present
      variables

   2) The negation comes down to 
      changing the polarity of the last
      unit cube
  ==================================*/
void CompInfo::form_property()
{

  CLAUSE &C = Prop.back();
  assert(C.size() == 1);
  C[0] = -C[0];

} /* end of function form_property */

/*=================================

     F O R M _ B A D _ S T A T E S

  This function forms 'BadStates'
  in terms of the next  state variables

 ASSUMPTIONS:
   1) Currently 'Prop' specifies the
      bad states in terms of present
      variables

  ===============================*/
void CompInfo::form_bad_states()
{

  form_bad_states0(Bad_states);
  add_constr_nilits(Bad_states);
  
} /* end of function form_bad_states */


/*=================================

  F O R M _ B A D _ S T A T E S 0

  ===============================*/
void CompInfo::form_bad_states0(CNF &Bstates)
{

  
  htable_lits.change_marker(); // increment or reset the hash table marker 
  htable_lits.started_using();

  int marker = htable_lits.marker;
  CUBE &Table = htable_lits.Table;

  // mark present state variables

  for (size_t i=0; i < Pres_svars.size(); i++) {
    int var_ind = Pres_svars[i]-1;
    Table[var_ind] = marker; }

  for (size_t i=0; i < Prop.size(); i++) {
    CLAUSE &C = Prop[i];
    CLAUSE Res;
    for (size_t j=0; j < C.size(); j++) {
      int var_ind = abs(C[j])-1;

      // a present state variable
      if (Table[var_ind] == marker) {
	int var_ind1 = Pres_to_next[var_ind];
	if (var_ind1 < 0) {
	  p();
	  M->error() << "Pres_svars.size() = " << Pres_svars.size() 
		     << M->eom;
	  M->error() << "Next_svars.size() = " << Next_svars.size()
		     << M->eom;
	  throw(ERROR1);
	}
	if (C[j] < 0) Res.push_back(-(var_ind1+1));
	else Res.push_back(var_ind1+1);
	continue;}

      // not a present state variable
      if (C[j] > 0) Res.push_back(C[j]+max_num_vars0);
      else Res.push_back(-(-C[j]+max_num_vars0));
    }

    Bstates.push_back(Res);
  }
  
  htable_lits.done_using();
} /* end of function form_bad_states0 */

/*==============================

         F O R M _ C E X

  ==============================*/
void CompInfo::form_cex()
{

  if ((Cex.size() == 1) || (Cex.size() == 2))
    return; // trivial counterexample generated earlier

  assert(Obl_table.size() > 0);

  CUBE St_cube  =  Obl_table.back().St_cb;
  form_init_st(St_cube);
  Cex.push_back(St_cube);
 
  std::string Name = "Gen_sat";
  init_sat_solver(Gen_sat,max_num_vars,Name);

  accept_new_clauses(Gen_sat,Tr);

  DNF Inp_trace;
  form_inp_trace(Inp_trace);

  for (size_t i=0; i < Inp_trace.size(); i++) {
    MvecLits Assmps;
    add_assumps1(Assmps,Cex[i]);     
    add_assumps1(Assmps,Inp_trace[i]);
    bool sat_form = check_sat2(Gen_sat,Assmps);
    assert(sat_form);
    CUBE Nst,St;
    extr_cut_assgns1(Nst,Next_svars,Gen_sat);
    conv_to_pres_state(St,Nst);
    Cex.push_back(St);
  }

  delete_solver(Gen_sat);
} /* end of function form_cex */

/*========================================

           F O R M _ I N I T _ S T

  =========================================*/
void CompInfo::form_init_st(CUBE &St_cube)
{

  SCUBE S;

  array_to_set(S,St_cube);

  for (size_t i=0; i < Ist.size(); i++)  {
    CLAUSE &U = Ist[i];
    assert(U.size() == 1);
    if (S.find(U[0]) == S.end())
      St_cube.push_back(U[0]);
  }

  int diff = Pres_svars.size() - St_cube.size();
  assert(diff >= 0);

  if (diff > 0) {
    SCUBE S1;
    array_to_set(S1,St_cube);
    for (size_t i=0; i < Pres_svars.size(); i++) {
      int lit = Pres_svars[i];
      if (S1.find(lit) != S1.end()) continue;
      if (S1.find(-lit) != S1.end()) continue;
      St_cube.push_back(lit);
    }
   
  }

  assert(Pres_svars.size() == St_cube.size());


} /* end of function form_init_st */
