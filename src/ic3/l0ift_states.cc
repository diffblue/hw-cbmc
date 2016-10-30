/******************************************************

Module: Lifting states, i.e. turning states into 
        cubes of states (Part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include "Solver.h"
#include "SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

/*=======================================

     L I F T _ G O O D_ S T A T E

 ASSUMPTIONS:

   1) Nst_cube is given in terms of next
      state variables

 ======================================*/
void CompInfo::lift_good_state(CUBE &Gst_cube,CUBE &Prs_st,
                               CUBE &Inps,CUBE &Nst_cube)
{

  // add unit clauses specifying inputs
  MvecLits Assmps;
  CUBE Inps1;
  rem_constr_lits(Inps1,Inps,Constr_inp_lits);
  add_assumps1(Assmps,Inps1);
  

  // add clause excluding next state cube
  
  
  Mlit act_lit;  
  add_cls_excl_st_cube(act_lit,Lgs_sat,Nst_cube);
 
  Assmps.push(act_lit);

  CUBE Prs_st1;
  rem_constr_lits(Prs_st1,Prs_st,Constr_ps_lits);  
  add_assumps2(Assmps,Prs_st1);
  
  bool sat_form = check_sat2(Lgs_sat,Assmps);
  if (sat_form) {
    p();
    std::cout << "Inps-> " << Inps << std::endl;
    std::cout << "Prs_st-> " << Prs_st << std::endl;
    std::cout << "Nst_cube-> " << Nst_cube << std::endl;
    exit(100);
  }
  

  gen_state_cube(Gst_cube,Prs_st1,Lgs_sat);

  release_lit(Lgs_sat,~act_lit);

  num_gstate_cubes++;
  length_gstate_cubes += Gst_cube.size();
  add_constr_lits1(Gst_cube);


} /* end of function lift_good_state */

/*========================================

      L I F T _ B A D _ S T A T E 

  =========================================*/
void CompInfo::lift_bad_state(CUBE &Bst_cube,CUBE &St,CUBE &Inps)
{

  TrivMclause Assmps;

  CUBE Inps1;
  rem_constr_lits(Inps1,Inps,Constr_inp_lits);

  add_assumps1(Assmps,Inps1);

  CUBE St1;
  rem_constr_lits(St1,St,Constr_ps_lits);
  add_assumps2(Assmps,St1);

 
  bool sat_form = check_sat2(Lbs_sat,Assmps);
 
  if (sat_form) {
    assert(Fun_coi_lits.size() > 0);
    Bst_cube = St;
    return;
  }

  gen_state_cube(Bst_cube,St1,Lbs_sat);
 
  num_bstate_cubes++;
  length_bstate_cubes += Bst_cube.size();

  add_constr_lits1(Bst_cube);

} /* end of function lift_bad_state */


/*==========================================

    G E N _ S T A T E _ C U B E 
 
   ASSUMPTIONS:
    1) Formula S.D is unsatisfiable
    2) S.Proof is a proof of that

 ========================================*/
void CompInfo::gen_state_cube(CUBE &St_cube,CUBE &St,SatSolver &Slvr)
{

 
 
  Minisat::Solver *Mst = Slvr.Mst;
  for (int i=0; i < St.size(); i++) {
    Mlit L = conv_to_mlit(St[i]);
    if (Mst->conflict.has(~L)) {
      St_cube.push_back(St[i]); 
    } 	
  }	
  
} /* end of function gen_state_cube */


/*==========================================

  A D D _ C L S _ E X C L _ S T _ C U B E

  ===========================================*/
void CompInfo::add_cls_excl_st_cube(Mlit &act_lit,SatSolver &Slvr,CUBE &St)
{
  CLAUSE C;
  act_lit = Minisat::mkLit(Slvr.Mst->newVar(),false);
  int lit = Minisat::var(act_lit)+1;
  C.push_back(-lit);


  for (int i=0; i < St.size(); i++) {
    int var_ind = abs(St[i])-1;
    C.push_back(-St[i]);
  }

 
  // add literals constraining internal variables

  for (int i=0; i < Tr_coi_lits.size(); i++) {
    int lit = Tr_coi_lits[i];
    int var_ind = abs(lit)-1;
    assert (Var_info[var_ind].type == INTERN);
    C.push_back(-lit);
  }

  accept_new_clause(Slvr,C);
  
} /* end of function add_cls_excl_st_cube */



/*=============================================

        E X T R _ N E X T _ I N P S

 This function returns the set of assignments
 to next state time frame inputs mapped to present
 state time frame.

  ASSUMPTIONS:
 1) Sat-solver 'S' just proved formula satisfiable
 2) Input variables of the next state time frame
    are those of the present time frame shifted
    by 'max_num_vars0'
 3) Assignment returned by 'S' is actually the
    negation of a satisfying assignment
    
  =============================================*/
void CompInfo::extr_next_inps(CUBE &Inps,SatSolver &Slvr)
{

  MboolVec &S = Slvr.Mst->model;

  for (int i=0; i < Inp_vars.size(); i++) {
    int orig_var_ind = Inp_vars[i]-1;
    int var_ind = orig_var_ind + max_num_vars0;
    assert(var_ind < max_num_vars);
    if (S[var_ind] == Mtrue) Inps.push_back(orig_var_ind+1);
    else Inps.push_back(-(orig_var_ind+1));
  }

 
} /* end of function extr_next_inps */
