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

/*====================================================

        P R I N T _ O N E _ B R A N C H _ P R O P

  ====================================================*/
void CompInfo::print_one_branch_prop(int num,GateNames &Gn,
                                  GateToLit &Gate_to_lit)
{


  CUBE Vars;

  find_most_act(Vars,num);
  
 
  printf("assert property (~p0 ");


  for (size_t i=0; i < Vars.size(); i++) {
    int var_ind =  Vars[i]-1;
    int gate_ind = var_ind;
    assert(Gate_to_lit.find(gate_ind) != Gate_to_lit.end());
    literalt lit = Gate_to_lit[gate_ind];
    unsigned ind = lit.var_no();
    assert(ind <= Gn.size());
    
    printf(" || ");
    if (lrand48() % 2)  std::cout << "~";                               
    std::cout << Gn[ind];
  }


  printf(");\n");
  

  

} /* end of function print_one_branch_prop */

/*=====================================

        P R I N T _ B R A N C H

  ====================================*/
void CompInfo::print_branch(CUBE &Vars,size_t num,GateNames &Gn,
                            GateToLit &Gate_to_lit)
{

  for (size_t i=0; i < Vars.size(); i++) {
    int var_ind =  Vars[i]-1;
    int gate_ind = var_ind;
    assert(Gate_to_lit.find(gate_ind) != Gate_to_lit.end());
    literalt lit = Gate_to_lit[gate_ind];
    unsigned ind = lit.var_no();
    assert(ind <= Gn.size());
    
    printf(" || ");
    if ((num & (1 << i)) == 0)  std::cout << "~";                               
    std::cout << Gn[ind];
  }



} /* end of function print_branch */

/*====================================================

          P R I N T _ B R A N C H _ P R O P S

  ====================================================*/
void CompInfo::print_branch_props(int num,GateNames &Gn,
                                  GateToLit &Gate_to_lit)
{


  CUBE Vars;

  find_most_act(Vars,num);
  
  size_t max_val = 1 << Vars.size();

  for (size_t i=0; i < max_val; i++) {
    printf("assert property (~p0 ");
    print_branch(Vars,i,Gn,Gate_to_lit);
    printf(");\n");
  }

  

} /* end of function print_branch_props */



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
  //print_sorted_act(V);
  
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





