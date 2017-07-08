/******************************************************

Module: CNF Generation (Part 3)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <fstream>
#include <set>
#include <map>
#include <algorithm>
#include <queue>

#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

/*==================================

      A D D _ C O N S T R S

  ==================================*/
void CompInfo::add_constrs() 
{
  M->status() << "adding " << Constr_ilits.size() + Constr_nilits.size()
	      << " unit constraints" << M->eom;
  for (size_t i=0; i < Constr_ilits.size(); i++) {
    CLAUSE U;
    U.push_back(Constr_ilits[i]);
    Tr.push_back(U);
  }

  SCUBE::iterator pnt;
  for (pnt = Constr_nilits.begin(); pnt != Constr_nilits.end(); pnt++) {
    CLAUSE U;
    U.push_back(*pnt);
    Tr.push_back(U);
  }

} /* end of function add_constrs */

/*==============================

  E M P T Y _ C U B E

  This function returns 'true'
  if cube C contains opposite 
  literals. Otherwise, the 
  function returns 'false'.
  ==============================*/
bool empty_cube(CUBE &C)
{SCUBE Lits;

  for (size_t i=0; i < C.size(); i++) {
    if (Lits.find(-C[i]) != Lits.end())
      return(true); // empty cube
    Lits.insert(C[i]);
  }

  return(false);

} /* end of function empty_cube */

/*=========================

  F O R M _ I N D E X

  ==========================*/
int form_index(CUBE &C)
{
  int result = 0;
  for (size_t i=0; i < C.size();i++)
    {assert(abs(C[i]) == i+1);
      if (C[i] > 0)  result |= 1 << i;
    }

  return(result);

} /* end of function form_index */

/*================================================

     G E N _ T R A N S _ R E L

  This function is obtained from 'add_time_frame'
  and 'shift' is a "legacy parameter".

  =================================================*/
void CompInfo::gen_trans_rel(int shift)
{

  for (size_t i=0; i < N->Gate_list.size();i++) {
    int gate_ind = Ordering[i];
    Gate &G =  N->Gate_list[gate_ind];
    if (G.gate_type == INPUT) continue;
    if (G.gate_type == LATCH) continue;
// skip the gates that are not part of the transition function
    if (G.flags.transition == 0) 
      if (G.flags.tran_constr == 0) continue; 
    switch (G.func_type)
      {case CONST:
	  add_const_gate_cube(Tr,gate_ind,shift);
	  break;
      case AND:   
	add_and_gate_cubes(Tr,gate_ind,shift);
	break;
      case OR:  
	add_or_gate_cubes(Tr,gate_ind,shift);
	break;
      case BUFFER: 
	add_buffer_gate_cubes(Tr,gate_ind,shift);
	break;
      case TRUTH_TABLE: 
	add_truth_table_gate_cubes(Tr,gate_ind,shift);         
	break;
      case COMPLEX: 
        M->error() << "complex gates are not allowed" << M->eom;
	throw(ERROR1);
      default:   
        M->error() << "wrong gate type" << M->eom;
	throw(ERROR1);
      }
  }

} /* end of function gen_trans_rel */

 

/*====================================

  P R I N T _ V A R _ I N D E X E S

  ====================================*/
void CompInfo::print_var_indexes(const char *fname)
{


  std::ofstream Out_str(fname,std::ios::out);
  if (!Out_str) {
    M->error() << "cannot open file " << std::string(fname) << M->eom;
    throw(ERROR2);}

  DNF topol_levels;
  
  fill_up_levels(N,topol_levels);
  CCUBE marked_vars;
  marked_vars.assign(2*N->Gate_list.size(),0);

  // print var indexes in topological order
  for (size_t i=0; i <= N->max_levels; i++) {    
    Out_str << "--------------------------------------\n";
    Out_str << "topological level " << i << "\n";
    CUBE &Gates = topol_levels[i];
    for (size_t j=0; j < Gates.size(); j++) {
      int gate_ind = Gates[j];
      Gate &G = N->get_gate(gate_ind);
      switch (G.gate_type)
	{case LATCH: Out_str << "L: ";
	    break;
	case INPUT: Out_str << "I: ";
	  break;
	case GATE: Out_str << "G: ";
	  break;
	default: assert(false);
	}
      fprint_name(Out_str,G.Gate_name);
      Out_str << "  " << Gate_to_var[gate_ind] << "\n";
      int tmp = Gate_to_var[gate_ind];
      if (marked_vars[tmp] != 0) 
	Out_str << "variable " << tmp <<  " is shared!!\n";
	  
    marked_vars[tmp] = 1;
  }
}
Out_str.close();

}/* end of function print_var_indexes */

/*=========================================

      S E T _ C O N S T R _ F L A G

  ==========================================*/
void CompInfo::set_constr_flag()
{

  for (size_t i=0; i < N->Gate_list.size();i++) {
    Gate &G = N->get_gate(i);
    G.flags.label = 0;  
    G.flags.fun_constr = 0;
    G.flags.tran_constr = 0;}


  ConstrGates::iterator pnt;

  for (pnt = Constr_gates.begin(); pnt!=Constr_gates.end(); pnt++)  {
    CUBE Gates;
    CUBE Stack;
    int gate_ind = pnt->first;
    Gate &G = N->get_gate(gate_ind);
    if (G.gate_type == LATCH) continue;
    if (G.gate_type == INPUT) continue;
    Stack.push_back(gate_ind);
    bool tran_flag,fun_flag;

    gen_constr_coi(Gates,tran_flag,fun_flag,Stack);
    tran_flag = true;
    fun_flag = true;  
  
    mark_constr_gates(Gates,tran_flag,fun_flag);
    if (tran_flag) Constr_gates[gate_ind].tran_coi = 1;
    else Constr_gates[gate_ind].tran_coi = 0;
    if (fun_flag) Constr_gates[gate_ind].fun_coi = 1;
    else Constr_gates[gate_ind].fun_coi = 0;
  }
  


} /* end of function set_constr_flag */


