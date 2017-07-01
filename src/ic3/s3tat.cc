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
  std::cout << std::fixed;
  std::cout.precision(1);
  std::cout << "#svars = " << Pres_svars.size() << ", aver. bst. cube = "
	    << av_bc_size << ", aver. gst. cube = " << av_gc_size << "\n";
 

} /* end of function print_lifting_stat */


/*==============================

     P R I N T _ F L A G S

  ============================*/
void CompInfo::print_flags()
{

  std::cout << "rem_subsumed_flag = " << rem_subsumed_flag << "\n";

  //  LIT_PICK_HEUR
  // 
  std::cout << "lit_pick_heur = ";
  switch (lit_pick_heur) {
  case RAND_LIT:
    std::cout << "RAND_LIT\n";
    break;
  case INACT_LIT:
    std::cout << "INACT_LIT\n";
    break;
  case INACT_VAR:
    std::cout << "INACT_VAR\n";
    break;
  case FIXED_ORDER:
    std::cout << "FIXED_ORDER\n";
    break;
  default:
    assert(false);
  }


  //  ACT_UPD_MODE
  // 
  std::cout << "act_upd_mode = ";
  switch (act_upd_mode) {
  case NO_ACT_UPD:
    std::cout << "NO_ACT_UPD\n";
    break;
  case TF_ACT_UPD:
    std::cout << "TF_ACT_UPD\n";
    break;
  case MINISAT_ACT_UPD:
    std::cout << "MINISAT_ACT_UPD\n";
    break;
  default:
    assert(false);
  }

  //  print sort modes
  // 

  std::cout << "sorted objects = ";
  if (sorted_objects == LITS) std::cout << "LITS\n";
  else if (sorted_objects == VARS) std::cout << "VARS\n";
  else assert(false);

  print_induct_lift_sort_mode("lift_sort_mode",lift_sort_mode);
 
  print_induct_lift_sort_mode("ind_cls_sort_mode",ind_cls_sort_mode);

  print_gate_sort_mode();
  std::cout << "selector = " << selector << "\n";
  std::cout << "ctg_flag = " << ctg_flag << "\n";
  std::cout << "constr_flag = " << constr_flag << "\n";
  std::cout << "standard_mode = " << standard_mode << "\n";
 



} /* end of function print_flags */


/*==========================================================

    P R I N T _ I N D U C T _ L I F T _ S O R T _ M O D E

  =========================================================*/
void CompInfo::print_induct_lift_sort_mode(const char *mode_name,int sort_mode) 
{
  std::cout << std::string(mode_name) << "= ";
  switch (sort_mode) {
  case NO_SORT:
    std::cout << "NO_SORT\n";
    break;
  case FULL_SORT:
    std::cout << "FULL_SORT\n";
    break;
  case PART_SORT:
    std::cout << "PART_SORT\n";
    std::cout << "max_num_elems = " << max_num_elems << "\n";
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

  std::cout << "gate_sort_mode = ";
  switch (gate_sort_mode) {
  case INIT_SORT:
    std::cout << "INIT_SORT";
    break;
  case INPS_FIRST:
    std::cout << "INPS_FIRST";
    break;
  case OUTS_FIRST:
    std::cout << "OUTS_FIRST";
    break;
  case RAND_SORT:
    std::cout << "RAND_SORT";
    break;
  default:
    assert(false);
  }

  std::cout << "\n";

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
