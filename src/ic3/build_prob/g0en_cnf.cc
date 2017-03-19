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

int debug_flag=0;

/*======================

  G E N _ C N F S

  =====================*/
void  CompInfo::gen_cnfs(char *fname,bool print_flag)
{  
  int total_ngates = N->Gate_list.size();  
  int shift = total_ngates - N->nlatches; // we subtract latches
 
  assign_var_indexes();

  
 
  char fname1[MAX_NAME];

  if (print_flag) {
    // print index file
    strcpy(fname1,fname);
    strcat(fname1,".ind");
    print_var_indexes(fname1);
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
  for (int i=0; i < N->Gate_list.size(); i++) {
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

  int count = 0;
  for (int i=0; i < N->Gate_list.size();i++) {
    int gate_ind = Ordering[i];
    Gate &G =  N->Gate_list[gate_ind];
    if (G.gate_type == INPUT) continue;
    if (G.gate_type == LATCH) continue;
// skip the gates that are not part of the output function
    if (G.flags.output_function == 0) 
      if (G.flags.fun_constr == 0) continue; 
    if (short_version)
// skip the gates that are shared by transition relation and out function
      if (G.flags.transition) continue; 
    int var_ind = Gate_to_var[gate_ind]-1;
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
        printf("complex gates are not allowed\n");
	exit(1);
      default:   
	printf("wrong gate type\n");
	exit(1);
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
  for (int i=0; i < N->Latches.size();i++) {
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
    defaul:
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

  // form indexes 
  Gate &G =  N->Gate_list[gate_ind];
 
  int var_ind = Gate_to_var[gate_ind] + shift;

  CUBE C;
  assert(G.F.size() < 2);
  if (G.F.size() == 1) C.push_back(var_ind + shift);
  else if (G.F.size() == 0) C.push_back(-(var_ind + shift));
  if (debug_flag) std::cout << C << " 0\n";

  F.push_back(C);

 
} /* end of function add_const_gate_cube */

/*=================================================

  A D D _ B U F F E R _ G A T E _ C U B E S

  ================================================*/
void CompInfo::add_buffer_gate_cubes(DNF &F,int gate_ind,int shift)
{

  // form indexes 
  CUBE var_indexes;
  Gate &G = N->Gate_list[gate_ind];


  for (int i=0; i < G.Fanin_list.size();i++) {
    int gate_ind1 =  G.Fanin_list[i];
    int var_ind = Gate_to_var[gate_ind1];
    var_indexes.push_back(var_ind);
  }

  // add the output var
  var_indexes.push_back(Gate_to_var[gate_ind]);

  CUBE C;
  // first cube
  if (G.Polarity[0] == 0)  C.push_back(var_indexes[0]+shift);  
  else C.push_back(-(var_indexes[0]+shift));
  C.push_back(-(var_indexes[1]+shift)); 
  F.push_back(C);
  if (debug_flag) std::cout << C << " 0\n";

  // second cube
  C.clear();
  if (G.Polarity[0] == 0)  C.push_back(-(var_indexes[0]+shift));  
  else C.push_back(var_indexes[0]+shift);
  C.push_back(var_indexes[1]+shift);
  F.push_back(C);
  if (debug_flag) std::cout << C << " 0\n";

} /* end of function add_buffer_gate_cubes */
