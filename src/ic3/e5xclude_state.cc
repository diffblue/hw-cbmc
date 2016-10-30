/******************************************************

Module:  Excludes a state from which a bad state is
         reachable (Part 5)

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

/*=====================================

      A D J U S T _ C L A U S E 2

  This function remove the literals of C
  that are satisfied by an assignment 
  contained in 'St_cube'. So on
  exit, cube ~C overlaps with St_cube

  ASSUMPTIONS:
    St_cube in general contains more than
    one assignment

  =====================================*/
bool CompInfo::adjust_clause2(CLAUSE &C,CUBE &St_cube,SCUBE &Failed_lits)
{

  if (verbose > 3) {
    printf("%*c",9,' ');
    printf("expand_clause\n");
  }
  htable_lits.change_marker(); 
  htable_lits.started_using();

  int marker = htable_lits.marker;
  CUBE &Table = htable_lits.Table;

  for (int i=0; i < St_cube.size(); i++) {
    int var_ind = abs(St_cube[i])-1;
    if (St_cube[i] < 0) Table[var_ind] = marker;
    else Table[var_ind+max_num_vars] = marker;
  }

  int shift = 0;
  for (int i=0; i < C.size(); i++) {
    int var_ind = abs(C[i])-1;
    if ((Table[var_ind+max_num_vars] == marker) && (C[i] < 0)) {
      C[i-shift] = C[i]; // value assigned to 'var_ind+1'  of 'St_cube' 
      continue; } //falsifies the corresponding literal of C
                 

    if ((Table[var_ind] == marker) && (C[i] > 0)) { 
      C[i-shift] = C[i];
      continue; // the same reason as above
    }

    shift++; // remove literal C[i]
    if (Failed_lits.find(C[i]) != Failed_lits.end())  {
      htable_lits.done_using();
      return(false);
    }
  }

  if (shift == 0) {
    p();
    exit(1); }

  C.resize(C.size()-shift);
  htable_lits.done_using();

  return(true);
} /* end of function adjust_clause2 */


/*==============================================

          T R I V _ I N D _ C L S _ P R O C

  ============================================*/
bool CompInfo::triv_ind_cls_proc(CLAUSE &Res,CLAUSE &C,int tf_ind)
{

  bool ok = triv_ind_cls(tf_ind,C);
  if (ok) Res = C;

  return(ok);

} /* end of function triv_ind_cls_proc */
/*============================================

   F I N D _ I N D _ S U B C L A U S E _ C T G

  If (reset_flag == 'false'),
  Icb_sat is not reset when
  formula is unsatisfaible

  ==========================================*/
bool CompInfo::find_ind_subclause_ctg(CLAUSE &C,int curr_tf,CLAUSE &C0,
		       	char st_descr,int rec_depth,SCUBE &Failed_lits)
{

  if (verbose > 2) {
    printf("find_ind_subclause_ctg\n");
}

  SatSolver &Slvr = Time_frames[curr_tf].Slvr;

  C = C0;


  // MAIN LOOP

  int ctg_cnt = 0;
  while(true)  {
    
    // add assumptions
    MvecLits Assmps;
    Mlit act_lit;  
    add_temp_clause(act_lit,Slvr,C);
    Assmps.push(act_lit);

    if (st_descr == NEW_STATE) add_negated_assumps2(Assmps,C,false);
    else add_negated_assumps2(Assmps,C,true);

    // run a SAT-check
    

    bool sat_form = check_sat2(Slvr,Assmps);
  
    // inductive clause is found
    if (sat_form == false) {// C is the longest inductive clause
      CLAUSE C1,C2;
      gen_assump_clause(C1,Slvr,Assmps);
      conv_to_pres_state(C2,C1);
      if (!corr_clause(C2)) modif_ind_clause(C2,C);     
      C = C2;
      release_lit(Slvr,~act_lit);
      return(true);     
    }

    
    // inductive clause is not found yet
    CUBE Ctg_st,Inps,Nxt_st;
    extr_cut_assgns1(Ctg_st,Pres_svars,Slvr);
    extr_cut_assgns1(Nxt_st,Next_svars,Slvr);
    extr_cut_assgns1(Inps,Inp_vars,Slvr);

    release_lit(Slvr,~act_lit);

    CUBE Ctg_cube;
  
    bool succ;
    if ((ctg_cnt < max_ctg_cnt) && (rec_depth < max_rec_depth))    {
      CUBE Nxt_cube;
      use_coi_to_drop_svars(Nxt_cube,Nxt_st,tf_lind-curr_tf-1);
      lift_ctg_state(Ctg_cube,Ctg_st,Inps,Nxt_cube);
      ctg_cnt++;
      tot_ctg_cnt++;
      succ = exclude_ctg(Ctg_cube,curr_tf,rec_depth);
      if (succ) {
	succ_ctg_cnt++;
	continue;
      }
    }

    bool ok;
    ok = adjust_clause2(C,Ctg_cube,Failed_lits);
    if (!ok) return(false);
    // adjust_clause1(C,Ctg_cube);
    ok = corr_clause(C);
    if (!ok)  return(false);
    ctg_cnt = 0;
  }

} /* end of function find_ind_clause_ctg */

/*================================

      T R I V _ I N D _ C L S 

  ================================*/
bool CompInfo::triv_ind_cls(int tf_ind,CLAUSE &C)
{

  SatSolver &Slvr = Time_frames[tf_ind].Slvr;

  MvecLits Assmps;
  Mlit act_lit;  
  add_temp_clause(act_lit,Slvr,C);
  Assmps.push(act_lit);

  add_negated_assumps2(Assmps,C,false);

  bool sat_form = check_sat2(Slvr,Assmps);
  release_lit(Slvr,~act_lit);

  return(!sat_form);
} /* end of function triv_ind_cls */



/*================================

       S U B S U M E S

  This function returns 'true'
  if every literal of 'C' is 
  marked in 'Ht'

  ==============================*/
bool CompInfo::subsumes(CLAUSE &C,hsh_tbl &Ht)
{

  int marker = Ht.marker;
  CUBE &Table = Ht.Table;

  for (int i=0; i < C.size(); i++) {
    int var_ind = abs(C[i])-1;
    if (C[i] < 0) {
      if (Table[var_ind] != marker) 
	return(false);}
    else // C[i] > 0
      if (Table[var_ind+max_num_vars] != marker)
	return(false);
  }

  return(true);
  


} /* end of function subsumes */
