/******************************************************

Module: Printing out some statistics of an IC3 run
        (Part 2)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>
#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

/*=======================================

   P R I N T _ L I F T I N G _ S T A T

  ======================================*/
void CompInfo::print_lifting_stat()
{

  if (num_bstate_cubes == 0) return;
  if (num_gstate_cubes == 0) return;

  float av_bc_size = length_bstate_cubes / num_bstate_cubes;
  float av_gc_size = length_gstate_cubes / num_gstate_cubes;
  M->statistics() << std::fixed;
  M->statistics().precision(1);
  M->statistics() << "#svars = " << Pres_svars.size() << ", aver. bst. cube = "
	    << av_bc_size << ", aver. gst. cube = " << av_gc_size << M->eom;
 

} /* end of function print_lifting_stat */


/*==============================

     P R I N T _ F L A G S

  ============================*/
void CompInfo::print_flags()
{

  M->statistics() << "rem_subsumed_flag = " << rem_subsumed_flag << M->eom;

  //  LIT_PICK_HEUR
  // 
  M->statistics() << "lit_pick_heur = ";
  switch (lit_pick_heur) {
  case RAND_LIT:
    M->statistics() << "RAND_LIT" << M->eom;
    break;
  case INACT_LIT:
    M->statistics() << "INACT_LIT" << M->eom;
    break;
  case INACT_VAR:
    M->statistics() << "INACT_VAR" << M->eom;
    break;
  case FIXED_ORDER:
    M->statistics() << "FIXED_ORDER" << M->eom;
    break;
  default:
    assert(false);
  }


  //  ACT_UPD_MODE
  // 
  M->statistics() << "act_upd_mode = ";
  switch (act_upd_mode) {
  case NO_ACT_UPD:
    M->statistics() << "NO_ACT_UPD" << M->eom;
    break;
  case TF_ACT_UPD:
    M->statistics() << "TF_ACT_UPD" << M->eom;
    break;
  case MINISAT_ACT_UPD:
    M->statistics() << "MINISAT_ACT_UPD" << M->eom;
    break;
  default:
    assert(false);
  }

  //  print sort modes
  // 

  M->statistics() << "sorted objects = ";
  if (sorted_objects == LITS) M->statistics() << "LITS" << M->eom;
  else if (sorted_objects == VARS) M->statistics() << "VARS" << M->eom;
  else assert(false);

  print_induct_lift_sort_mode("lift_sort_mode",lift_sort_mode);
 
  print_induct_lift_sort_mode("ind_cls_sort_mode",ind_cls_sort_mode);

  print_gate_sort_mode();
  M->statistics() << "selector = " << selector  << M->eom;
  M->statistics() << "ctg_flag = " << ctg_flag  << M->eom;
  M->statistics() << "constr_flag = " << constr_flag  << M->eom;
  M->statistics() << "standard_mode = " << standard_mode  << M->eom;
 



} /* end of function print_flags */


/*==========================================================

    P R I N T _ I N D U C T _ L I F T _ S O R T _ M O D E

  =========================================================*/
void CompInfo::print_induct_lift_sort_mode(const char *mode_name,int sort_mode) 
{
  M->statistics() << std::string(mode_name) << "= ";
  switch (sort_mode) {
  case NO_SORT:
    M->statistics() << "NO_SORT" << M->eom;
    break;
  case FULL_SORT:
    M->statistics() << "FULL_SORT" << M->eom;
    break;
  case PART_SORT:
    M->statistics() << "PART_SORT" << M->eom;
    M->statistics() << "max_num_elems = " << max_num_elems << "" << M->eom;
    break;
  default:
    assert(false);
  }
} /* end of function print_induct_lift_sort_mode */

/*===========================================

  P R I N T _ G A T E _ S O R T _ M O D E

  =========================================*/
void CompInfo::print_gate_sort_mode()
{

  M->statistics() << "gate_sort_mode = ";
  switch (gate_sort_mode) {
  case INIT_SORT:
    M->statistics() << "INIT_SORT";
    break;
  case INPS_FIRST:
    M->statistics() << "INPS_FIRST";
    break;
  case OUTS_FIRST:
    M->statistics() << "OUTS_FIRST";
    break;
  case RAND_SORT:
    M->statistics() << "RAND_SORT";
    break;
  default:
    assert(false);
  }

  M->statistics()  << M->eom;

} /* end of function print_gate_sort_mode */

/*===========================================

         I N I T _ I N D _ C L S

  This function returns the number of clauses
  of Ist that have been pushed from the 
  initial time frame

  Assumptions: 
   1) The first 'Ist.size()' clauses of 'F'
      specify the initial states
 ============================================*/
int CompInfo::init_ind_cls()
{

  int count = 0;
  for (size_t i=0; i < Ist.size(); i++) 
    if (Clause_info[i].span > 0) count++;

  
  return(count);

} /* end of function init_ind_cls */
