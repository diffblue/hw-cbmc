/******************************************************

Module: Computes over-approximation for a new time
        frame

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

  N E X T _ T I M E _ F R A M E

  Returns:
  0 - property holds
  1 - property failed
  2 - undecided
  3 - time exceeded

  ===============================*/
int CompInfo::next_time_frame()
{

 
  M->status() << "-------------" << M->eom;
  M->status() << "next_time_frame" << M->eom;
  M->status() << "tf_lind = " << tf_lind << M->eom;
  M->status() << "F.size() = " << F.size() <<  ", #inact. clauses "
	    << num_inact_cls << M->eom;
 
  int ret_val = 2;
  
  add_time_frame();
  empty_cnts();
  init_bst_sat_solver();

  bool triv_time_frame = true;
  while (true) {
    bool sat_form = check_sat1(Bst_sat);
    if (sat_form == false) {
      ret_val = 2;
      break;}

    triv_time_frame = false;
    CUBE Nst,St,Inps;
    extr_cut_assgns1(Nst,Next_svars,Bst_sat);
    extr_next_inps(Inps,Bst_sat);
    
    conv_to_pres_state(St,Nst);
    CLAUSE Bst_cube;
    lift_bad_state(Bst_cube,St,Inps);
    CUBE Pst;
    extr_cut_assgns1(Pst,Pres_svars,Bst_sat);
    Inps.clear();
    extr_cut_assgns1(Inps,Inp_vars,Bst_sat);
    CUBE Gst_cube,Nxt_bst_cube;
    conv_to_next_state(Nxt_bst_cube,Bst_cube);
    lift_good_state(Gst_cube,Pst,Inps,Nxt_bst_cube);
   

    CNF G;  
    int min_tf;
    exclude_state_cube(G,min_tf,Gst_cube,Inps);
   
    Time_frames[tf_lind].num_pbss++;
    if (time_to_terminate()) return(3);
    
    if (Pr_queue.size() > 0) {// a counterexample is found      
      ret_val = 1;
      break;}

    // no counterexample
   
    assert(Pr_queue.size() == 0);
    accept_new_clauses(Bst_sat,G);
  }

  delete_solver(Bst_sat);
 
  if (ret_val != 2)   return(ret_val);  

  if (rem_subsumed_flag) rem_redund_clauses();  
  simplify_tf_solvers();
  Lgs_sat.Mst->simplify();
  push_clauses_forward(triv_time_frame); 
 
  if (inv_ind >= 0) return(0);    

  if (Time_frames[tf_lind].num_bnd_cls == 0) {
    inv_ind = tf_lind;
    return(0);}
    
  return(2);

} /* end of function next_time_frame */




/*==========================================

  T I M E _ T O _ T E R M I N A T E

  ==========================================*/
bool CompInfo::time_to_terminate() {
  excl_st_count++;
  if (time_limit > 0) {
    double usrtime,systime;
    get_runtime (usrtime, systime);
    if (usrtime > time_limit) return(true);
  }
  return(false);
} /* end of function time_to_terminate */

/*====================================

  A D D _ T I M E _ F R A M E

  ====================================*/
void CompInfo::add_time_frame()
{

  TimeFrame Tf;
 
  Tf.num_pbss = 0;
  Tf.tot_num_ctis = 0;
  Tf.num_rcnt_ctis = 0;
  Tf.num_bnd_cls = 0;
  Tf.num_seen_cls = 0;
  Tf.num_redund_cls = 0;

  Time_frames.push_back(Tf);

  init_time_frame_solver(Time_frames.size()-1); 

} /* end of function add_time_frame */


/*=============================

  E M P T Y _ C N T S

  ============================*/
void CompInfo::empty_cnts() 
{

  for (int i=0; i <= tf_lind; i++)
    Time_frames[i].num_rcnt_ctis = 0;

} /* end of function empty_cnts */


