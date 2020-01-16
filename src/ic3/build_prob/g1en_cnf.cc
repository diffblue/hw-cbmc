/******************************************************

Module: CNF Generation (Part 2)

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

extern bool empty_cube(CUBE &C);
extern int form_index(CUBE &C);


/*=====================

  M A K E _ C U B E 

  =====================*/
void  make_cube(int index,int ninputs,CUBE &C)
{
  C.clear();
  for (int i=0; i < ninputs; i++)
    if (index & (1 << i)) C.push_back(i+1);
    else C.push_back(-(i+1));
} /* end of function make_cube */

/*================================================

  A D D _ O R _ G A T E _ C U B E S

  ==================================================*/
void  CompInfo::add_or_gate_cubes(DNF &F,int gate_ind,int shift)
{


  // form indices 
  CUBE var_indices;
  Gate &G =  N->Gate_list[gate_ind];


  for (size_t i=0; i < G.Fanin_list.size();i++) {
    int gate_ind1 = G.Fanin_list[i];
    int var_ind = Gate_to_var[gate_ind1];
    var_indices.push_back(var_ind);
  }


  // add the output var
  var_indices.push_back(Gate_to_var[gate_ind]);

  //
  // generate the long clause
  //
  CUBE C;
  for (size_t i=0; i <  G.Fanin_list.size();i++)
    if (G.Polarity[i] == 0)   C.push_back(var_indices[i]+shift); 
    else C.push_back(-(var_indices[i]+shift)); 
  C.push_back(-(var_indices.back()+shift));
  if (!empty_cube(C))  F.push_back(C);

  //
  //  generate short claueses
  //
  //
  for (size_t i=0; i < G.Fanin_list.size();i++)
    {C.clear();
      if (G.Polarity[i] == 0)   C.push_back(-(var_indices[i]+shift)); 
      else C.push_back(var_indices[i]+shift); 
      C.push_back(var_indices.back()+shift);
      if (!empty_cube(C)) F.push_back(C);
    }


} /* end of function add_or_gate_cubes */

/*========================================

  A D D _ A N D _ G A T E _ C U B E S

  =======================================*/
void CompInfo::add_and_gate_cubes(DNF &F,int gate_ind,int shift)
{

  // form indices 
  CUBE var_indices;
  Gate &G =  N->Gate_list[gate_ind];
    
  for (size_t i=0; i < G.Fanin_list.size();i++) {
    int gate_ind1 = G.Fanin_list[i];
    int var_ind = Gate_to_var[gate_ind1];
    var_indices.push_back(var_ind);
  }

  // add the output var
  var_indices.push_back(Gate_to_var[gate_ind]);
 

  //
  // generate the long clause
  //
  CUBE C;
  for (size_t i=0; i < G.Fanin_list.size();i++)
    if (G.Polarity[i] == 0)   C.push_back(-(var_indices[i]+shift)); 
    else C.push_back(var_indices[i]+shift); 
  C.push_back(var_indices.back()+shift);
  if (!empty_cube(C))  F.push_back(C);

  //
  //  generate short claueses
  //
  //
  for (size_t i=0; i < G.Fanin_list.size();i++) {
    C.clear();
    if (G.Polarity[i] == 0)   C.push_back(var_indices[i]+shift); 
    else C.push_back(-(var_indices[i]+shift)); 
    C.push_back(-(var_indices.back()+shift));
    if (!empty_cube(C)) F.push_back(C);
  }

} /* end of function add_and_gate_cubes */

/*=======================================================

  A D D _ T R U T H _ T A B L E _ G A T E _ C U B E S

  ======================================================*/
void  CompInfo::add_truth_table_gate_cubes(DNF &F,int gate_ind,int shift)
{

  // form indices 
  CUBE var_indices;
  Gate &G =  N->Gate_list[gate_ind];

 
  for (size_t i=0; i < G.Fanin_list.size();i++) {
    int gate_ind1 = G.Fanin_list[i];
    int var_ind = Gate_to_var[gate_ind1];
    var_indices.push_back(var_ind);
  }

  // add the output var
  var_indices.push_back(Gate_to_var[gate_ind]);

  CUBE TT(1 << G.ninputs);
  for (size_t i=0; i < TT.size(); i++)
    TT[i] = 0;

  DNF &D = G.F;
  for (size_t i=0; i < D.size(); i++) {
    int index=form_index(D[i]);
    TT[index] = 1;
  }

  // form the cubes describing the ON-set
  for (size_t i=0; i < D.size();i++) {
    CUBE &C = D[i];
    CUBE C1;
    for (size_t j=0; j < C.size(); j++) {
      C1.push_back(var_indices[abs(C[j])-1]+shift);
      if (C[j] > 0) C1[j] = -C1[j];
    }
    C1.push_back(var_indices.back()+shift);
    if (!empty_cube(C1)) F.push_back(C1);
  }

  // form the cubes describing the OFF-set

  for (size_t i=0; i < TT.size(); i++)
    {CUBE C,C1;
      if (TT[i] == 1) continue;
      make_cube(i,G.ninputs,C);
      for (size_t j=0; j < C.size(); j++)
	{C1.push_back(var_indices[abs(C[j])-1]+shift);
	  if (C[j] >  0) C1[j] = -C1[j];
	}
      C1.push_back(var_indices.back()+shift);
      C1.back() = -C1.back();
      if (!empty_cube(C1)) F.push_back(C1);
    }

} /* end of function add_truth_table_gate_cubes */

