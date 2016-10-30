/*********************************************************

Module: Computes an inductive clause excluding a counter-
        example to generalization (Part 2)

Author: Eugene Goldberg, eu.goldberg@gmail.com

*********************************************************/
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

/*================================================

     U S E _ C O I _ T O _ D R O P _ S V A R S

  ASSUMPTIONS:
     1) Nxt_st is specified in terms of next state
        variables

  =================================================*/
void CompInfo::use_coi_to_drop_svars(CUBE &Nxt_cube,CUBE &Nxt_st,int dist)
{

  
  assert(dist >= 0);

  if (dist >=  Coi_svars.size()) {
    Nxt_cube = Nxt_st;
    return;
  }

  CUBE &Vars = Coi_svars[dist];

  // mark Coi vars
  htable_lits.change_marker();
  htable_lits.started_using();
  int marker = htable_lits.marker;
  CUBE &Table = htable_lits.Table;

  for (int i=0; i < Vars.size(); i++) {
    int pres_var_ind = Vars[i]-1;
    int nxt_var_ind = Pres_to_next[pres_var_ind];
    assert(nxt_var_ind >= 0);
    Table[nxt_var_ind]  = marker;
  }


  // keep only marked variables
  for (int i=0; i < Nxt_st.size(); i++) {
    int var_ind = abs(Nxt_st[i])-1;
    if (Table[var_ind] == marker) Nxt_cube.push_back(Nxt_st[i]);
  }

  htable_lits.done_using();
  

} /* end of function use_coi_to_drop_svars */

/*=======================================

     L I F T _ C T G _ S T A T E

 ======================================*/
void CompInfo::lift_ctg_state(CUBE &Ctg_cube,CUBE &Ctg_st,CUBE &Inps,
                              CUBE &Nst_cube)
{


  gcount++;

  // add unit clauses specifying inputs
  MvecLits Assmps;
  add_assumps1(Assmps,Inps);
  

  Mlit act_lit;  
  add_cls_excl_st_cube(act_lit,Lgs_sat,Nst_cube);
 
  Assmps.push(act_lit);
  add_assumps2(Assmps,Ctg_st);
  
  bool sat_form = check_sat2(Lgs_sat,Assmps);
  if (sat_form) {
    p();
    printf("Ctg_st.size() = %d, Nst_cube.size() = %d\n",(int) Ctg_st.size(),
          (int) Nst_cube.size());    
    printf("tf_lind = %d\n",tf_lind);
    exit(1);
  }
    
  gen_state_cube(Ctg_cube,Ctg_st,Lgs_sat);

  release_lit(Lgs_sat,~act_lit);


} /* end of function lift_ctg_state */

