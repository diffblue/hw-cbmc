/******************************************************

Module: Pushing clauses to later time frames (Part 2)

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


/*======================================

  S I M P L I F Y _ T F _ S O L V E R S

  =======================================*/
void CompInfo::simplify_tf_solvers()
{

  for (int i=1; i < Time_frames.size(); i++)
    Time_frames[i].Slvr.Mst->simplify();

} /* end of function simplify_tf_solvers */
/*====================================

      A D D  _ C O P I E S

  This function adds clause C  to 
  every i-th time frame where 
  i < 0 < tf_ind

  =====================================*/
void CompInfo::add_copies(int tf_ind,CLAUSE &C)
{

  for (int i=tf_ind; i > 0; i--) 
    add_one_copy(i,C);
  

} /* end of function add_copies */

/*==========================================

      A D D _ O N E _ C O P Y

  This function adds C to time frame 'tf_ind'

  ==========================================*/
void CompInfo::add_one_copy(int tf_ind,CLAUSE &C)
{

  accept_new_clause(Time_frames[tf_ind].Slvr,C);
  

} /* end of function add_one_copy */



/*====================================

       I N I T _ F I E L D S

  ====================================*/
void CompInfo::init_fields()
{

  for (int i=0; i < F.size(); i++) {
    if (Clause_info[i].active == 0) continue;
    Clause_info[i].skip = 0;
    Clause_info[i].delay = 0;
  }

} /* end of function init_fields */
