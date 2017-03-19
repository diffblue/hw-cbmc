/******************************************************

Module: Creation of tables relating present and next
        state variables

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

/*================================================

       C O N V _ T O _ N E X T _ S T A T E

   This function takes in a state represented
   in terms of pres state variables and converts
   it into the same state expressed in terms
   of next state variables

 =================================================*/
void CompInfo::conv_to_next_state(CUBE &A,CUBE &B)
{


  for (int i=0; i < B.size(); i++) {
    int var_ind = abs(B[i])-1;
    int var_ind1 = Pres_to_next[var_ind];
    assert(var_ind1 >= 0);
    if (B[i] < 0) A.push_back(-(var_ind1+1));
    else A.push_back(var_ind1+1);
  }

} /* end of function conv_to_next_state */

/*================================================

       C O N V _ T O _ P R E S _ S T A T E

   This function takes in a state represented
   in terms of next state variables and converts
   it into the same state expressed in terms
   of present state variables

 =================================================*/
void CompInfo::conv_to_pres_state(CUBE &A,CUBE &B)
{
 
  for (int i=0; i < B.size(); i++) {
    int var_ind = abs(B[i])-1;
    int var_ind1 = Next_to_pres[var_ind];
    assert(var_ind1 >= 0);
    if (B[i] < 0) A.push_back(-(var_ind1+1));
    else A.push_back(var_ind1+1);
  }

} /* end of function conv_to_pres_state */
