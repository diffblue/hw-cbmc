/******************************************************

Module: Functions used to complete creation of
        a sequential circuit (Part 2)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <queue>
#include <stdio.h>
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "r0ead_blif.hh"



/*=====================================================

  F I N I S H _ L E V E L S _ F R O M _ O U T P U T S

  ======================================================*/
void finish_levels_from_outputs(Circuit *N)
{

  for (int i=0; i < N->Gate_list.size();i++) {
    Gate &G = N->Gate_list[i];
    if (G.level_from_outputs < 0)
      G.level_from_outputs = N->max_levels;	
  }
  

} /* end of function finish_levels_from_outputs */

/*==================================================

  P R I N T _ L E V E L S _ F R O M _ O U T P U T S

  ====================================================*/
void print_levels_from_outputs(Circuit *N)
{

  for (int i=0; i < N->Gate_list.size();i++) {
    Gate &G =  N->Gate_list[i];
    print_name1(G.Gate_name);
    printf(": %d\n",G.level_from_outputs);
  }

 
} /* end of function print_levels_from_outputs */
/*================================================================

  C H E C K _ L E V E L S_ O F _ O U T P U T S

  Returns 0 if a fanout gate G1  of G is marked and is not assigned
  a level (this means that G1 is in the stack and N has a cycle).
  Otherwise it returns 1.

  If all fanout nodes of G are assigned levels, then on exit, 
  the 'level' variable  contains the maximum of levels of all fanout
  nodes. Otherwise, 'level' is equal to -1. All the fanout nodes that 
  are not assigned levels are added to the stack.
  =================================================================*/
int check_levels_of_outputs(Gate &G,Circuit *N,int &level,
			    CUBE &stack,bool &all_latches)
{ CUBE &Fanout_list = G.Fanout_list;
  

  all_latches = true;
  bool all_assigned = true;
  level = -1;
 
  for (int i=0; i < Fanout_list.size();i++)
    {Gate &G1 = N->Gate_list[Fanout_list[i]];

      if (G1.gate_type != LATCH) all_latches = false;

      if (G1.level_from_outputs >= 0)
	{if ((G1.level_from_outputs > level) && (all_assigned))
	    level = G1.level_from_outputs;
	  continue;
	}
      // G1 is not assigned a level yet
   
      if (G1.flags.label != 0) {
	print_name1(G1.Gate_name); 
        printf(" is visited but no level is assigned\n");
	return(0); // G1 is in the stack, there is a loop in the circuit
      }

      all_assigned = false; // mark the fact that fanout contains unass. gates
      if (G1.gate_type != LATCH)  
// add the gate to the stack unless it is a latch
	stack.push_back(Fanout_list[i]); 
    }

  if (!all_assigned)  
    level = -1;

  return(1);
}/* end of function check_levels_of_outputs  */
/*====================================================================

  A S S I G N _ L E V E L S _ F R O M _ O U T P U T S 1

  The function assigns levels to the gates of the subcircuit
  to which there is a path from the input node 'inp_num'. The function
  returns 0 if the subcircuit contains a cycle. Otherwise
  it returns 1
  =====================================================================*/
int assign_levels_from_outputs1(Circuit *N,int inp_num)
{CUBE stack;
  int level;

  stack.push_back(inp_num); // stack initialization

  GCUBE &Gate_list = N->Gate_list;
 
  while (stack.size() > 0) {
    // extract the 'top' gate numeric label
   
    int gate_num =  stack.back();

    
    Gate &G = Gate_list[gate_num];
    
    G.flags.label = 1;   
    if (G.Fanout_list.size() == 0) {// an output 
      G.level_from_outputs = 0;
      stack.pop_back();
      continue;
    }
    
    bool all_latches;
    if (check_levels_of_outputs(G,N,level,stack,all_latches) == 0)
      return(0); // the subcircuit contains a cycle
    
    if (level >= 0) {
      if ((G.gate_type != LATCH) && (!all_latches))  
   // level of G equals the maximum level of an input plus 1
          G.level_from_outputs = level + 1;    
	else G.level_from_outputs = 0;
	stack.pop_back();           
      }
  }
  return(1);

}/* end of function assign_levels_from_outputs1 */
/*==============================================================

  A S S I G N _ L E V E S _ F R O M _ O U T P U T S

  This function assign topological levels to the gates. Levels are
  numbered   from outputs (an output node that does not feed
  any other output node  is assigned level 0).
 
  The function also checks if N is asyclic. 


  ASSUMPTIONS:
  1) If G is a latch, then G.level_from_outputs is initialized
  to 0
  2) Otherwise, G is initialized to -1

  3) N->max_levels is already set (when computing levels
  from inputs)
  ==============================================================*/
void assign_levels_from_outputs(Circuit *N)
{
  clear_labels(N); 

  for (int i=0; i < N->Inputs.size();i++) {
    Gate &G = N->get_gate(N->Inputs[i]);
    if (assign_levels_from_outputs1(N,N->Inputs[i]) == 0) {
      std::cout << "Circuit '"; 
      print_name1(N->Circuit_name); 
      std::cout << "' has a cycle\n";
      exit(1);
    }
  }

 
  for (int i=0; i < N->Latches.size();i++) {
    Gate &G = N->get_gate(N->Latches[i]);
    if (assign_levels_from_outputs1(N,N->Latches[i]) == 0) {
      std::cout << "Circuit '"; 
      print_name1(N->Circuit_name); 
      std::cout << "' has a cycle\n";
      exit(1);
    }
  }

  finish_levels_from_outputs(N);

}/* end of function assign_levels_from_outputs */


/*================================================================

  C H E C K _ L E V E L S_ O F _ I N P U T S

  Returns 0 if a fanin gate G1  of G is marked and is not assigned
  a level (this means that G1 is in the stack and N has a cycle).
  Otherwise it returns 1.

  If all fanin nodes of G are assigned levels, then on exit, 
  the 'level' variable  contains the maximum of levels of all fanin
  nodes. Otherwise, 'level' is equal to -1. All the fanin nodes that 
  are not assigned levels are added to the stack.
  =================================================================*/
int check_levels_of_inputs(Gate &G,Circuit *N,int &level,
			   CUBE &stack)
{ CUBE &Fanin_list = G.Fanin_list;
  bool all_assigned = true;
  level = -1;
  for (int i=0; i < Fanin_list.size();i++) {
    Gate &G1 = N->Gate_list[Fanin_list[i]];
    if (G1.level_from_inputs >= 0) {
      if ((G1.level_from_inputs > level) && (all_assigned))
	level = G1.level_from_inputs;
      continue;
    }
    // G1 is not assigned a level yet
   
    if (G1.flags.label != 0)
      return(0); // G1 is in the stack, there is a loop in the circuit

    all_assigned = false; // mark the fact that fanin contains unassigned gates
    stack.push_back(Fanin_list[i]); // add the gate to the stack   
  }
  if (!all_assigned)  
    level = -1;

  return(1);
}/* end of function check_levels_of_inputs  */

/*==========================================================

  A S S I G N _ L E V E L S _ F R O M _ I N P U T S 1

  The function assigns levels to the gates of the subcircuit
  feeding the output with numeric lable 'out_num'. The function
  returns 0 if the subcircuit contains a cycle. Otherwise
  it returns 1
  ==========================================================*/

int assign_levels_from_inputs1(Circuit *N,int out_num)
{CUBE stack;
  int level;

  stack.push_back(out_num); // stack initialization
 
  GCUBE &Gate_list = N->Gate_list;

  while (stack.size() > 0) {
    // extract the 'top' gate numeric label
    int gate_num =  stack.back();
    
    Gate &G = Gate_list[gate_num];
    G.flags.label = 1;
    if (check_levels_of_inputs(G,N,level,stack) == 0)
      return(0); // the subcircuit contains a cycle
    if (level >= 0) {
      if (G.gate_type != LATCH) G.level_from_inputs = level + 1;    
      // level of G equals the maximum level of an input plus 1
      stack.pop_back(); 
      if (G.level_from_inputs > N->max_levels)
	N->max_levels = G.level_from_inputs;
    }
  }
  return(1);

}/* end of function assign_levels_from_inputs1 */

/*==============================================================

  A S S I G N _ L E V E S _ F R O M _ I N P U T S

  This function assign topological levels to the gates. Levels are
  numbered   from inputs (an input node is assigned level 0).
 
  The function also checks if N is asyclic. 
  ==============================================================*/
void assign_levels_from_inputs(Circuit *N)
{
  clear_labels(N); 

  for (int i=0; i < N->Outputs.size();i++)
    if (assign_levels_from_inputs1(N,N->Outputs[i]) == 0) {
      std::cout << "Circuit '"; 
      print_name1(N->Circuit_name); 
      std::cout << "' has a cycle\n";
      exit(1);
    }

  for (int i=0; i < N->Latches.size();i++)
    if (assign_levels_from_inputs1(N, N->Latches[i]) == 0) {
      std::cout << "Circuit '"; 
      print_name1(N->Circuit_name); 
      std::cout << "' has a cycle\n";
      exit(1);
    }
}/* end of function assign_levels_from_inputs */
