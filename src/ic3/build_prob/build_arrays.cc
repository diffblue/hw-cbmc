/******************************************************

Module: Functions specifying and relating input,
        present state and next state variables

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <set>
#include <map>
#include <algorithm>
#include <queue>

#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

/*==========================================

     F O R M _ I N P _ V A R S

===========================================*/
void CompInfo::form_inp_vars()
{
  for (int i=0; i < N->Inputs.size();i++) {
    int gate_ind = N->Inputs[i];
    int var = Gate_to_var[gate_ind];      
    Inp_vars.push_back(var);
  }

} /* end of function form_inp_vars */


/*==============================================

   F O R M _ P R E S _ S T A T E _ V A R S 

===============================================*/
void CompInfo::form_pres_state_vars()
{
  for (int i=0; i < N->Gate_list.size();i++) {
    Gate &G = N->get_gate(i);
    if (G.gate_type != LATCH) continue;
    int var = Gate_to_var[i];      
    Pres_svars.push_back(var);
  }

} /* end of function form_pres_state_vars */


/*===============================================

   F O R M  _ N E X T _ S T A T E _ V A R S 

===============================================*/
void CompInfo::form_next_state_vars()
{

  for (int i=0; i < N->Gate_list.size();i++) {
     Gate &G = N->get_gate(i);
      if (G.flags.feeds_latch == 0) continue;
      int var = Gate_to_var[i];      
      Next_svars.push_back(var);
     }


} /* end of function form_next_state_vars */

/*================================================

   F O R M _ N E X T _ T O _ P R E S _ C O N V

 ===============================================*/
void CompInfo::form_next_to_pres_conv()
{

  CUBE Pairs;
  
  for (int i=0; i < N->Gate_list.size();i++) {
    Gate &G = N->get_gate(i);
    if (G.flags.feeds_latch == 0) continue;
    int next_var = Gate_to_var[i]; 
    int latch_ind;   
    find_latch(N,G,latch_ind);
    int var = Gate_to_var[latch_ind];
    Pairs.push_back(next_var);
    Pairs.push_back(var);
  }

  form_table(Next_to_pres,Pairs,max_num_vars);

} /* end of function form_next_to_pres_conv */

/*================================================

   F O R M _ P R E S _ T O _ N E X T _ C O N V

 ===============================================*/
void CompInfo::form_pres_to_next_conv()
{

  CUBE Pairs;
  
  for (int i=0; i < N->Gate_list.size();i++) {
    Gate &G = N->get_gate(i);
    if (G.flags.feeds_latch == 0) continue;
    int next_var = Gate_to_var[i]; 
    int latch_ind;   
    find_latch(N,G,latch_ind);
    int var = Gate_to_var[latch_ind];
    Pairs.push_back(var);
    Pairs.push_back(next_var);     
  }

  form_table(Pres_to_next,Pairs,max_num_vars);

} /* end of function form_pres_to_next_conv */
