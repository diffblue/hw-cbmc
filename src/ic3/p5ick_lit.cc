/******************************************************

Module:  Picking a literal to remove when generalizing
         an inductive clause (Part 1)

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


/*=============================

    F X D _ O R D _ I N I T

  ============================*/
void CompInfo::fxd_ord_init(CLAUSE &B,CUBE &Avail_lits,SCUBE &Tried)
{

  for (int i=0; i < Avail_lits.size(); i++) {
    int lit = Avail_lits[i];
    if (Tried.find(lit) == Tried.end()) {
      B.push_back(lit);
      return;
    }
  }

  assert(false); // shouldn't reach this line

} /* end of function fxd_ord_init */

/*=======================

  F X D _ O R D _ L I T

  ======================*/
int CompInfo::fxd_ord_lit(CUBE &Curr,SCUBE &Tried)
{

  for (int i=0; i < Curr.size(); i++) {
    int lit = Curr[i];
    if (Tried.find(lit) == Tried.end())
      return(lit);
  }

  assert(false); // shouldn't reach this line

} /* end of function fxd_ord_lit */
