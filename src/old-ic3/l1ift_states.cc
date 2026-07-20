/******************************************************

Module: Lifting states, i.e. turning states into 
        cubes of states (Part 2)

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

/*========================================

         R E M _ C O N S T R _ L I T S

  ========================================*/
void CompInfo::rem_constr_lits(CUBE &Lits1,CUBE &Lits0,SCUBE &Constr_lits)
{

  for (size_t i=0; i < Lits0.size(); i++) 
    if (Constr_lits.find(Lits0[i]) == Constr_lits.end())
      Lits1.push_back(Lits0[i]);

} /* end of function rem_constr_lits */

/*============================================

       A D D _ C O N S T R _ L I T S 1

  =============================================*/
void CompInfo::add_constr_lits1(CUBE &St_cube)
{

  SCUBE::iterator pnt;

  for (pnt = Constr_ps_lits.begin(); pnt != Constr_ps_lits.end(); pnt++)
    St_cube.push_back(*pnt);

} /* end of function add_constr_lits1 */
