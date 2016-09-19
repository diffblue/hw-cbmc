/******************************************************

Module:  Excludes a state from which a bad state is
         reachable (Part 4)

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

/*=========================================

    P I C K _ L I T _ T O _ R E M O V E

  ========================================*/
int CompInfo::pick_lit_to_remove(CLAUSE &Curr,SCUBE &Tried,int curr_tf)
{

  int lit;
  switch (lit_pick_heur) {
  case RAND_LIT:
    lit = find_rand_lit(Curr,Tried);
    break;
  case INACT_LIT:
    lit = find_inact_lit(Curr,Tried,Lit_act0,Lit_act1);
    break;
  case INACT_VAR:
    lit = find_inact_var(Curr,Tried,Lit_act0,Lit_act1);
    break;
  case FIXED_ORDER:
    lit = fxd_ord_lit(Curr,Tried);
    break;
  default:
    printf("lit_pick_heur = %d\n",lit_pick_heur);
    exit(100);
  }

  return(lit);

} /* end of function pick_lit_to_remove */

/*=======================================

     G E N _ A S S U M P _ C L A U S E

  =======================================*/
void CompInfo::gen_assump_clause(CLAUSE &C,SatSolver &Slvr,MvecLits &Assmps)
{

  Minisat::Solver *S = Slvr.Mst;
  for (int i=0; i < Assmps.size(); i++) {
    Mlit L = ~Assmps[i];
    if (S->conflict.has(L)) {
      if (Minisat::var(L) >= Slvr.init_num_vars) continue; // skip activation literals (if any)
      int lit = mlit_to_lit(S,L);
      C.push_back(lit);
    }
  }
        

} /* end of function gen_assump_clause */
/*=========================================

     F O R M _ R E S _ C N F 

  This function returns a clause implied 
  by the formula of 'Time_frames[tf_ind].Slvr'
  that is falsified by 'St_cube'. This clause 
  if optimized in length

  ASSUMPTIONS:
   1) Every state of 'St_cube' falsifies a
      clause of 'Time_frames[tf_ind].Slvr'

  ========================================*/
void CompInfo::form_res_cnf(CNF &G,int tf_ind,CUBE &St_cube)
{
 
  SatSolver &Slvr = Time_frames[tf_ind].Slvr;
  MvecLits Assmps;
  add_assumps1(Assmps,St_cube);
  
  bool sat_form = Slvr.Mst->solve(Assmps);
  assert(sat_form == false);
  CLAUSE C;
  gen_assump_clause(C,Slvr,Assmps);
  G.push_back(C);

} /* end of function form_res_cnf */

/*=============================================

      C O N T _ I N I T _ S T A T E S

  =============================================*/
bool CompInfo::cont_init_states(CUBE &St_cube) {

  CLAUSE C;
  form_lngst_clause(C,St_cube);
  return(!corr_clause(C));

} /* end of function cont_init_states */

/*====================================================

        O B L I G _ I S _ A C T I V E

  =====================================================*/
bool CompInfo::oblig_is_active(int tf_ind,CUBE &St_cube)
{

  if (tf_ind >  tf_lind) return(false);

  SatSolver &Slvr = Time_frames[tf_ind].Slvr;

  MvecLits Assmps;
  add_assumps1(Assmps,St_cube);

  bool sat_form = check_sat2(Slvr,Assmps);

  return(sat_form);

} /* end of function oblig_is_active */

/*====================================

      A D D _ N E W _ E L E M

  =====================================*/
void CompInfo::add_new_elem(CUBE &St_cube,CUBE &Inp_assgn,
	      int tf_ind,int dist,int succ_ind,char descr)
{

  OblTableElem Dummy;
  Obl_table.push_back(Dummy);
  OblTableElem &El = Obl_table.back();
  El.St_cb = St_cube;
  El.Inp_assgn = Inp_assgn;
  El.tf_ind = tf_ind;
  El.dist = dist;
  El.succ_ind = succ_ind;
  El.st_descr = descr;
 

  if (descr == NEW_STATE) new_state_cnt++;
  else if (descr == OLD_STATE)
    old_state_cnt++;
  else {
    assert(descr == ROOT_STATE);
    root_state_cnt++;
  }
  
  PqElem El1;
  El1.tf_ind = tf_ind;
  El1.tbl_ind = Obl_table.size()-1;
  Pr_queue.push(El1);

} /* end of function add_new_elem */




/*=========================================

  M O D I F _ I N D _ C L A U S E

  ASSUMPTIONS:

  1) Ist -> C
  2) Ist !-> C1
  3) Lits(C1) is a strict subset of Lits(C)
  4) The set of initial states forms a cube

  This functions add to C1 a literal of C
  to make C1 satisfy all initial states

  ==========================================*/
void CompInfo::modif_ind_clause(CLAUSE &C1,CLAUSE &C)
{

  SCUBE Lits_Ist;

  for (int i=0; i < Ist.size(); i++) {
    CUBE &U = Ist[i];
    assert(U.size() == 1);
    Lits_Ist.insert(U[0]);
  }
  

  for (int i=0; i < C.size(); i++) {
    if (Lits_Ist.find(C[i]) == Lits_Ist.end())
      continue;
    C1.push_back(C[i]);
    break;
  }
  

} /* end of function modif_ind_clause */


