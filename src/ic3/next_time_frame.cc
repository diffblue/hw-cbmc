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
#include "Solver.h"
#include "SimpSolver.h"
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

  if (verbose == 0) {
    printf("-------------\n");
    printf("next_time_frame\n");
    printf("tf_lind = %d\n",tf_lind);
    printf("F.size() = %d, #inact. clauses %d\n",(int) F.size(),num_inact_cls);
  }
  

  int ret_val = 2;
  
  add_time_frame();
  empty_cnts();
  init_bst_sat_solver();
 
  while (true) {
    bool sat_form = check_sat1(Bst_sat);
    if (sat_form == false) {
      ret_val = 2;
      break;}

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
    CUBE Gst_cube;
    lift_good_state(Gst_cube,Pst,Inps,Bst_cube);
   

    CNF G;  
    int min_tf;
    exclude_state_cube(G,min_tf,Gst_cube,Inps);
    if (verbose > 0) 
      if (min_tf < tf_lind - 1) printf("min_tf = %d\n",min_tf);
    Time_frames[tf_lind].num_pbss++;
    if (time_to_terminate()) return(3);
    
    if (Pr_queue.size() > 0) {// a counterexample is found      
      ret_val = 1;
      break;}

    // no counterexample
   
    assert(Pr_queue.size() == 0);
    if (verbose >= 3) {
      if (G.size() == 1) {
	printf("inductive clause F[%d] is generated: ",(int) F.size());
	std::cout << G[0] << std::endl;}
      else printf("%d inductive CLAUSES are generated\n",(int) G.size());
    }

    accept_new_clauses(Bst_sat,G);
  }

  delete_solver(Bst_sat);
 
  if (ret_val != 2)   return(ret_val);  

  if (rem_subsumed_flag) rem_redund_clauses();  
  simplify_tf_solvers();
  Lgs_sat.Mst->simplify();
  push_clauses_forward(); 
 
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

  Time_frames.push_back(Tf);

  init_time_frame_solver(Time_frames.size()-1); 
  int ind = Time_frames.size()-1;

} /* end of function add_time_frame */


/*=============================

  E M P T Y _ C N T S

  ============================*/
void CompInfo::empty_cnts() 
{

  for (int i=0; i <= tf_lind; i++)
    Time_frames[i].num_rcnt_ctis = 0;

} /* end of function empty_cnts */


