/******************************************************

Module: CNF Generation (Part 4)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <set>
#include <map>
#include <algorithm>
#include <queue>

#include "Solver.h"
#include "SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "r0ead_blif.hh"
#include "m0ic3.hh"

/*=================================================

     A D D _ C O M P L E X _ G A T E _ C U B E S

  ================================================*/
void CompInfo::add_complex_gate_cubes(DNF &F,int gate_ind,int shift)
{

 // form indexes 
  CUBE var_indexes;
  Gate &G =  N->Gate_list[gate_ind];

  
  for (int i=0; i < G.Fanin_list.size();i++) {
    int gate_ind1 = G.Fanin_list[i];
    int var_ind = Gate_to_var[gate_ind1];
    var_indexes.push_back(var_ind);
  }

 // add the output var
  var_indexes.push_back(Gate_to_var[gate_ind]);
  
  DNF &D = G.F;
  // form the clauses describing the ON-set
  for (int i=0; i < D.size();i++) {
    CUBE &C = D[i];
    assert(C.size() > 0);
    CUBE C1;
    for (int j=0; j < C.size(); j++) {
      C1.push_back(var_indexes[abs(C[j])-1]+shift);
      if (C[j] > 0) C1[j] = -C1[j];
    }
    C1.push_back(var_indexes.back()+shift);
    F.push_back(C1);
  }

  DNF R;

  find_complem(R,D,G.ninputs);
  // check_overlapping_compl(R,D);
  // check_completeness(R,D,G.ninputs);

// form the clauses describing the OFF-set
  for (int i=0; i < R.size();i++) {
    CUBE &C = R[i];
    assert(C.size() > 0);
    CUBE C1;
    for (int j=0; j < C.size(); j++) {
      C1.push_back(var_indexes[abs(C[j])-1]+shift);
      if (C[j] > 0) C1[j] = -C1[j];
    }
    C1.push_back(var_indexes.back()+shift);
    C1.back() = -C1.back();
    F.push_back(C1);
  }

} /* end of function add_complex_gate_cubes */

/*=======================================

     M A R K _ C O N S T R _ G A T E S

  ======================================*/
void CompInfo::mark_constr_gates(CUBE &Gates,bool tran_flag,bool fun_flag)
{
  for (int i=0; i < Gates.size(); i++) {
    int gate_ind = Gates[i];
    Gate &G = N->get_gate(gate_ind);
    if (tran_flag) G.flags.tran_constr = 1;
    if (fun_flag) G.flags.fun_constr = 1;
  }

} /* end of function mark_constr_gates */

/*==============================================

          G E N _ C O N S T R _ C O I

  ===============================================*/
void CompInfo::gen_constr_coi(CUBE &Gates,bool &tran_flag,bool &fun_flag,
                             CUBE &Stack)
{

  tran_flag = false;
  fun_flag = false;

  assert(Stack.size() == 1);
  Gate &G = N->get_gate(Stack.back());
  assert(G.flags.label == 0);

  CUBE Labelled;

  while (Stack.size() > 0) {
    // printf("new iteration\n");
    int gate_ind = Stack.back();
    Stack.pop_back();
    Gate &G = N->get_gate(gate_ind);
    if (G.flags.label > 0) continue;
    
    G.flags.label = 1;
    Labelled.push_back(gate_ind);

    bool skip = false;
    if (G.flags.output_function > 0) {
      fun_flag = true;
      skip = true;
    }
    if (G.flags.transition > 0) {
      tran_flag = true;
      skip = true;
    }
    if (skip) continue;
    Gates.push_back(gate_ind);    

    // add fanin gates to the stack
    for (int i=0; i < G.Fanin_list.size(); i++) 
      Stack.push_back(G.Fanin_list[i]);
  }

  // remove label of Labelled
  for (int i=0; i < Labelled.size(); i++) {
    Gate &G = N->get_gate(Labelled[i]);
    G.flags.label = 0;
  }

} /* end of function gen_constr_coi */
