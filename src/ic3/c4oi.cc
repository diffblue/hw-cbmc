/*********************************************************

Module: Computes Cone Of Influence

Author: Eugene Goldberg, eu.goldberg@gmail.com

*********************************************************/
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

/*=============================
  
   F O R M _ C O I _ A R R A Y

  ==============================*/
void CompInfo::form_coi_array()
{

  DNF Coi_arr;

  CUBE Coi;

  CUBE Stack;
  assert(N->noutputs == 1);
  int gate_ind = N->Outputs[0];
  Stack.push_back(gate_ind);
  
  form_coi(Coi,Stack,htable_lits);
  
  if (Coi.size() == N->nlatches) return;
  

  Coi_arr.push_back(Coi);


  int level = 0;
  while (true) {
    if (Coi_arr.size() > max_coi_depth) break;
    CUBE Dcoi;
    form_stack(Stack,Coi_arr[level]);
    form_coi(Dcoi,Stack,htable_lits);
    if (Dcoi.size() == N->nlatches) break;
    Coi_arr.push_back(Dcoi);
    level++;
  }

  conv_gates_to_svars(Coi_arr);

} /* end of function form_cor_array */

/*===============================================

     C O N V _ G A T E S _ T O _ S V A R S

  ===============================================*/
void CompInfo::conv_gates_to_svars(DNF &Coi_arr)
{
  
  for (int i=0; i < Coi_arr.size(); i++) {
    CUBE &Gate_inds = Coi_arr[i];
    CUBE Vars;
    for (int j=0; j < Gate_inds.size(); j++) {
      int var = Gate_to_var[Gate_inds[j]];
      Vars.push_back(var);
    }
    Coi_svars.push_back(Vars);
  }


} /* end of function conv_gates_to_svars */

/*================================

         F O R M _ S T A C K

  ==============================*/
void CompInfo::form_stack(CUBE &Stack,CUBE &Latches)
{

  Stack.clear();
  for (int i=0; i < Latches.size(); i++) {
    int gate_ind = Latches[i];
    Gate &G = N->get_gate(gate_ind);
    assert(G.Fanin_list.size() == 1);
    int gate_ind1 = G.Fanin_list[0];
    Stack.push_back(gate_ind1);
  }

} /* end of function form_stack */

/*====================================

       F O R M _ C O I

  =====================================*/
void CompInfo::form_coi(CUBE &Coi,CUBE &Stack,hsh_tbl &Htbl)
{

  assert(N->Gate_list.size() < Htbl.size());

  Htbl.change_marker();
  Htbl.started_using();
  int marker = Htbl.marker;
  CUBE &Table = Htbl.Table;
 

  for (int i=0; i < Stack.size(); i++) 
    Table[Stack[i]] = marker;
 

  while (Stack.size() > 0) {
    int gate_ind = Stack.back();
   
    Gate &G = N->get_gate(gate_ind);
    if (G.gate_type == LATCH) {
      Stack.pop_back();
      Coi.push_back(gate_ind);
      continue;
    }
 

    if (G.gate_type == INPUT) {
      Stack.pop_back();
      continue;
    }   
    // add fanin gates   
    int added = 0;
    for (int i=0; i < G.ninputs; i++) {
      int gate_ind1 = G.Fanin_list[i];
      if (Table[gate_ind1] == marker) continue;
      Gate &G1 = N->get_gate(gate_ind1);
      if (G1.gate_type == INPUT) continue;
      Table[gate_ind1] = marker;
      Stack.push_back(gate_ind1);
      added++;
    }
    if (added == 0) Stack.pop_back();    
  }

  Htbl.done_using();

} /* end of function form_coi */


