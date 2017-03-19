/******************************************************

Module: Some Auxiliary Functions

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

/*===============================================

  F O R M _ P R O P E R T Y _ G A T E S

  ==============================================*/
void CompInfo::form_property_gates(CUBE &Gates)
{

  clear_labels(N);

  int outp_ind =  N->Outputs[0];
   
  CUBE Buffer;
  Buffer.push_back(outp_ind);
 

  while (Buffer.size() > 0)    {
    int gt_ind = Buffer.back();
    Buffer.pop_back();
    Gate &G = N->get_gate(gt_ind);
    if (G.flags.label)  continue;
  

    G.flags.label = 1;

     
    if (G.gate_type == LATCH) 
      continue;
     
    if (G.flags.feeds_latch)   
      continue;
      
    Gates.push_back(gt_ind);

      
    for (int i=0; i < G.Fanin_list.size();i++)  {
      int fanin_ind = G.Fanin_list[i];
      Buffer.push_back(fanin_ind);
    }

  } 

} /* end of function form_property_gates */

/*=============================================

      F I N D _ L A T C H

  This function returns the index 'latch_ind'
  of the latch fed by the output of 'G'.

  ==============================================*/
void find_latch(Circuit *N,Gate &G,int &latch_ind)
{
  

  for (int i=0; i < G.Fanout_list.size();i++) {
    int gate_ind = G.Fanout_list[i];
    Gate &G1 = N->get_gate(gate_ind);
    if (G1.gate_type == LATCH) {
      latch_ind = gate_ind;
      return;
    }

  }
  assert(false); // we shouldn't reach this line
} /* end of function find_latch */


/*=============================================

  A S S I G N _ V A R _ I N D E X E S

  =============================================*/
void CompInfo::assign_var_indexes()
{

  Gate_to_var.assign(N->Gate_list.size(),-1);
  int curr_index = 1;
  for (int i=0; i < N->Gate_list.size();i++) {
    Gate &G = N->get_gate(i);
    Gate_to_var[i]=curr_index++;
  }

  num_circ_vars = curr_index-1;
} /* end of function assign_var_indexes */
