/******************************************************

Module:  Some auxiliary functions (Part 5)

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




void CompInfo::print_branch_props(CUBE &Vars,GateNames &Gn,
                                  GateToLit &Gate_to_lit)
{



}



/*====================================================

            P R I N T _ S O R T E D _ A C T

  =====================================================*/
void CompInfo::print_sorted_act(std::vector <ActInd> &V)
{

  for (size_t i=0; i < V.size(); i++) {
    if ((i > 0) && (i % 10 == 0)) printf("\n");
    if ((i > 0) && (i % 10 != 0))  printf(" ");
    printf("(%1.f,%d)",V[i].first,V[i].second);
  }

  if (V.size() % 10 != 0) printf("\n");

} /* end of function print_sorted_act */



/*======================================

    S O R T _ B S T _ A C T I V I T Y

========================================*/
void CompInfo::sort_bst_activity(std::vector <ActInd> &V)
{

  //  form pairs
  
  for (size_t i=0; i < Pres_svars.size(); i++) {
    int var_ind = Pres_svars[i]-1;
    float act_val0 =  Bst_act0[var_ind];
    float act_val1 = Bst_act1[var_ind];
    
    float prod_val = act_val0 * act_val1;
    V.push_back(std::make_pair(prod_val,var_ind+1));
  }

 
  stable_sort(V.begin(),V.end(),sel_most_act());

} /* end of function sort_bst_activity */

/*=====================================

       F I N D _ M O S T _ A C T 

  ======================================*/
void CompInfo::find_most_act(CUBE &Vars,int num)
{


  std::vector <ActInd> V;
  
  sort_bst_activity(V);
  print_sorted_act(V);
  
  for (int i=0; i < num; i++) 
    Vars.push_back(V[i].second);


} /* end of function find_most_act */

/*======================================

    U P D _ B S T _ A C T I V I T Y

  ======================================*/
void CompInfo::upd_bst_activity(CUBE &S)
{


  for (size_t i=0; i < S.size(); i++) {
    int var_ind = abs(S[i])-1;
    if (S[i] < 0) Bst_act0[var_ind] += 1.;
    else Bst_act1[var_ind] += 1.;
  }


} /* end of function upd_bst_activity */





