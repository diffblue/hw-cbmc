/******************************************************

Module: Printing out some statistics of an IC3 run
        (Part 2)

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

/*=======================================

   P R I N T _ L I F T I N G _ S T A T

  ======================================*/
void CompInfo::print_lifting_stat()
{

  if (num_bstate_cubes == 0) return;
  if (num_gstate_cubes == 0) return;

  float av_bc_size = length_bstate_cubes / num_bstate_cubes;
  float av_gc_size = length_gstate_cubes / num_gstate_cubes;
  printf("#svars = %d, aver. bst. cube = %.1f, aver. gst. cube = %.1f\n",
	 (int) Pres_svars.size(),av_bc_size,av_gc_size);
 

} /* end of function print_lifting_stat */


/*==============================

     P R I N T _ F L A G S

  ============================*/
void CompInfo::print_flags()
{

  printf("rem_subsumed_flag = %d\n",rem_subsumed_flag);

  //  LIT_PICK_HEUR
  // 
  printf("lit_pick_heur = ");
  switch (lit_pick_heur) {
  case RAND_LIT:
    printf("RAND_LIT\n");
    break;
  case INACT_LIT:
    printf("INACT_LIT\n");
    break;
  case INACT_VAR:
    printf("INACT_VAR\n");
    break;
  case FIXED_ORDER:
    printf("FIXED_ORDER\n");
    break;
  default:
    assert(false);
  }


  //  ACT_UPD_MODE
  // 
  printf("act_upd_mode = ");
  switch (act_upd_mode) {
  case NO_ACT_UPD:
    printf("NO_ACT_UPD\n");
    break;
  case TF_ACT_UPD:
    printf("TF_ACT_UPD\n");
    break;
  case MINISAT_ACT_UPD:
    printf("MINISAT_ACT_UPD\n");
    break;
  default:
    assert(false);
  }

  //  print sort modes
  // 

  printf("sorted objects = ");
  if (sorted_objects == LITS) printf("LITS\n");
  else if (sorted_objects == VARS) printf("VARS\n");
  else assert(false);

  print_sort_mode("lift_sort_mode",lift_sort_mode);
 
  print_sort_mode("ind_cls_sort_mode",ind_cls_sort_mode);

  printf("selector = %d\n",selector);
  printf("ctg_flag = %d\n",ctg_flag);
  printf("constr_flag = %d\n",constr_flag);

  // print state of generalization heuristic
  printf("generalization heuristic = ");
  if (grl_heur == NO_JOINS) printf("NO_JOINS\n");
  else {
    assert(grl_heur == WITH_JOINS);
    printf("WITH_JOINS\n");
  }



} /* end of function print_flags */

/*=============================================

       P R I N T _ S O R T _ M O D E

  =============================================*/
void CompInfo::print_sort_mode(const char *mode_name,int sort_mode) 
{
  printf("%s = ",mode_name);
  switch (sort_mode) {
  case NO_SORT:
    printf("NO_SORT\n");
    break;
  case FULL_SORT:
    printf("FULL_SORT\n");
    break;
  case PART_SORT:
    printf("PART_SORT\n");
    printf("    max_num_elems = %d\n",max_num_elems);
    break;
  default:
    assert(false);
  }
} /* end of function print_sort_mode */
