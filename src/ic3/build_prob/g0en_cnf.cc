/******************************************************

Module: CNF Generation  (Part 1)

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

/*======================

  G E N _ C N F S

  =====================*/
void  CompInfo::gen_cnfs(const char *fname,bool print_flag)
{  
  assign_var_indices();
 

  if (print_flag) {
    // print index file
    print_var_indices(std::string(fname)+".ind");
  }

  gen_initial_state_cubes();

  set_constr_flag();

  gen_trans_rel(0);
  
  gen_out_fun(Prop,0,false);

  gen_out_fun(Short_prop,0,true);
 
}/* end of function gen_cnfs */
/*===============================

  A D D _ L A S T _ C U B E

  ==============================*/
void  CompInfo::add_last_cube(DNF &F)
{
  // find the output gate
  int gate_ind=-1;
  for (size_t i=0; i < N->Gate_list.size(); i++) {
    Gate &G =  N->Gate_list[i];
    if (G.flags.output == 1) {
      gate_ind = i;
      break;
    }
  }
  assert(gate_ind != -1);
  
  // generate the last cube
  CUBE C;
  int var = Gate_to_var[gate_ind];
  C.push_back(var);
  F.push_back(C);
} /* end of function add_last_cube */

/*=========================

  G E N _ O U T _ F U N

  =========================*/
void CompInfo::gen_out_fun(DNF &H,int shift,bool short_version)
{
  for (size_t i=0; i < N->Gate_list.size();i++) {
    int gate_ind = Ordering[i];
    Gate &G =  N->Gate_list[gate_ind];
    if (G.gate_type == INPUT) continue;
    if (G.gate_type == LATCH) continue;
// skip the gates that are not part of the output function
    if (G.flags.output_function == 0)
       if ((G.flags.fun_constr == 0) && (G.flags.tran_constr == 0)) 
    if (short_version)
// skip the gates that are shared by transition relation and out function
      if (G.flags.transition) continue; 
    switch (G.func_type)
      {case CONST:
	  add_const_gate_cube(H,gate_ind,shift);
	  break;
      case AND:   	
	add_and_gate_cubes(H,gate_ind,shift);       
	break;
      case OR:         
	add_or_gate_cubes(H,gate_ind,shift);      
	break;
      case BUFFER:    
	add_buffer_gate_cubes(H,gate_ind,shift);    
	break;
      case TRUTH_TABLE:         
	add_truth_table_gate_cubes(H,gate_ind,shift);                 
	break;
      case COMPLEX: 
	M->error() << "complex gates are not allowed" << M->eom;
	throw(ERROR1);
      default:   
	M->error() << "wrong gate type" << M->eom;
	throw(ERROR1);
      }
  }

  // add last cube
  add_last_cube(H);

} /* end of function gen_out_fun */


/*=====================================================

  G E N _ I N I T I A L _ S T A T E _ C U B E S

  ====================================================*/
void  CompInfo::gen_initial_state_cubes()
{
  for (size_t i=0; i < N->Latches.size();i++) {
    int gate_ind = N->Latches[i];
    Gate &G = N->get_gate(gate_ind);
    assert(G.gate_type == LATCH);
    CUBE C;
    switch (G.init_value) {
    case 0:
      C.push_back(-Gate_to_var[gate_ind]);
      break;
    case 1:
      C.push_back(Gate_to_var[gate_ind]);
      break;
    case 2:
      break;
    default:
      assert(false);
    }
    if (C.size() > 0) 
      Ist.push_back(C);
  }

} /* end of function gen_initial_state_cubes */



/*===========================================

  A D D _ C O N S T _ G A T E _ C U B E 

  ===========================================*/
void  CompInfo::add_const_gate_cube(DNF &F,int gate_ind,int shift)
{

  // form indices 
  Gate &G =  N->Gate_list[gate_ind];
 
  int var_ind = Gate_to_var[gate_ind] + shift;

  CUBE C;
  assert(G.F.size() < 2);
  if (G.F.size() == 1) C.push_back(var_ind + shift);
  else if (G.F.size() == 0) C.push_back(-(var_ind + shift));

  F.push_back(C);

 
} /* end of function add_const_gate_cube */

/*=================================================

  A D D _ B U F F E R _ G A T E _ C U B E S

  ================================================*/
void CompInfo::add_buffer_gate_cubes(DNF &F,int gate_ind,int shift)
{

  // form indices 
  CUBE var_indices;
  Gate &G = N->Gate_list[gate_ind];


  for (size_t i=0; i < G.Fanin_list.size();i++) {
    int gate_ind1 =  G.Fanin_list[i];
    int var_ind = Gate_to_var[gate_ind1];
    var_indices.push_back(var_ind);
  }

  // add the output var
  var_indices.push_back(Gate_to_var[gate_ind]);

  CUBE C;
  // first cube
  if (G.Polarity[0] == 0)  C.push_back(var_indices[0]+shift);  
  else C.push_back(-(var_indices[0]+shift));
  C.push_back(-(var_indices[1]+shift)); 
  F.push_back(C);

  // second cube
  C.clear();
  if (G.Polarity[0] == 0)  C.push_back(-(var_indices[0]+shift));  
  else C.push_back(var_indices[0]+shift);
  C.push_back(var_indices[1]+shift);
  F.push_back(C);

} /* end of function add_buffer_gate_cubes */
