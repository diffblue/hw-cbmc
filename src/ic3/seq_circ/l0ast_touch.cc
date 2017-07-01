/******************************************************

Module: Functions used to complete creation of
        a sequential circuit (Part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <queue>
#include <assert.h>
#include <stdio.h>
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "s0hared_consts.hh"

/*========================================

  F I L L _ F A N O U T _ L I S T S

  The function fills out the fanout lists 
  of the gates. We also check if there are 
  gate inputs that are defined neither
  as gates nor inputs
 
  ====================================-====*/
void fill_fanout_lists(Circuit *N)
{

  GCUBE &Gate_list = N->Gate_list;
  for (size_t i=0; i < Gate_list.size();i++) {
    Gate &G=Gate_list[i];
    // enumerate all the fanin nodes
    for (size_t j=0; j < G.Fanin_list.size();j++) {
      int k = G.Fanin_list[j];
      Gate &G1 = Gate_list[k]; // G1 is a fanin node of G
      // add numeric label of gate G to the fanout list of G1
      G1.Fanout_list.push_back(i);
    
      //  check if G1 is a hanging input 

      if (G1.flags.active == 0) {
	std::cout << "**   when processing the inputs of the gate ";
        print_name1(G.Gate_name); 
        std::cout << std::endl;
	std::cout << "it is found that  gate ";
        print_name1(G1.Gate_name);
        std::cout << " is not defined" << std::endl;
	throw(ERROR1);
      }     
    }
  }


} /* end of function fill_fanout_lists*/

/*=================================================

  C H E C K _ F A N O U T _ F R E E _ I N P U T S
 
  The function checks if there are "hanging" inputs
  ====================================================*/
void  check_fanout_free_inputs(Circuit *N)
{CUBE &Inputs= N->Inputs;

  for (size_t i=0; i < Inputs.size();i++) {
    Gate &I =  N->Gate_list[Inputs[i]];
    if (I.Fanout_list.size() == 0) {
      std::cout << "input "; 
      print_name1(I.Gate_name); 
      std::cout << " does not fan out\n";
    }

  }
 
}/* end of function check_fanout_free_inputs */
/*=======================================================

  A S S I G N _ G A T E _ T Y P E 

  The funciton assigns the GATE type to gates that
  are still have the type UNDEFINED. It also sets 
  the 'G.flags.output' flag if G is a primary output
 
  ======================================================*/
void assign_gate_type(Circuit *N,CDNF &Out_names,bool rem_dupl_opt)
{ 
 
  for (size_t i=0; i < Out_names.size();i++) {
    CCUBE &name = Out_names[i];
    if (N->Pin_list.find(name) == N->Pin_list.end()) {
      std::cout << "false output "; 
      print_name(&name); 
      std::cout << std::endl;
      throw(ERROR1);
    }
    int gate_num = N->Pin_list[name];
    N->Outputs.push_back(gate_num); // record the gate as a circuit output
    Gate &G = N->get_gate(gate_num);

    // we don't accept the blif file in which the output of 
    // a latch is also a primary output
    assert(G.gate_type != LATCH); 
    G.flags.output = 1;
    G.gate_type = GATE;  
  }

  N->noutputs = N->Outputs.size();
  //
  // assign gate types to the rest of the gates
  //

  for (size_t i=0; i < N->Gate_list.size();i++) {
    Gate &G =  N->Gate_list[i];
    if (G.gate_type != UNDEFINED)
      continue;
    if (!rem_dupl_opt)
      if (G.Fanout_list.size() == 0) {
	std::cout << "gate "; 
	print_name1(G.Gate_name); 
	std::cout << " does not fan out\n";
	throw(ERROR1);
      }
    G.gate_type = GATE;
  }

}/* end of function assign_gate_type */



/*=======================================================

  S E T _ O U T P U T _ F U N C T I O N _ F L A G

  =====================================================*/
void set_output_function_flag(Circuit *N,CUBE &stack)
{
  if (stack.size() == 0) return;
  int gate_ind = stack.back();
  stack.pop_back();
  Gate &G = N->get_gate(gate_ind);
  if (G.flags.label == 1) return;
 
  G.flags.label = 1;
  G.flags.output_function = 1;

  if (G.gate_type == INPUT) return;

  for (size_t i=0; i < G.ninputs; i++) {
    int fanin_gate_ind = G.Fanin_list[i];
    stack.push_back(fanin_gate_ind);
    set_output_function_flag(N,stack);
  }

} /* end of function set_output_function_flag */

/*=========================================

  S E T _ T R A N S I T I O N _ F L A G

  ========================================*/
void set_transition_flag(Circuit *N,CUBE &stack)
{

 
  if (stack.size() == 0) return;
  int gate_ind = stack.back();
  stack.pop_back();
  Gate &G = N->get_gate(gate_ind);
    
  if (G.flags.label == 1) return;

  G.flags.label = 1;
  G.flags.transition = 1;

  if (G.gate_type == INPUT) return;

  for (size_t i=0; i < G.ninputs; i++) {
    int fanin_gate_ind = G.Fanin_list[i];
    stack.push_back(fanin_gate_ind);
    set_transition_flag(N,stack);
  }

} /* end of function set_transition_flag */


/*============================================================


  S E T _ T R A N S _ O U T P U T _ F U N _ F L A G S

  This function sets the 'transition' and 'output_function'
  flags for the gates of N  


  =============================================================*/
void set_trans_output_fun_flags(Circuit *N)
{
 
  CUBE stack; 

  // mark the transition gates
  assert(N->Latches.size() == N->nlatches);
  clear_labels(N); // we do not need to clear labels in each iteration
  for (size_t i=0; i < N->Latches.size();i++)  {
    stack.clear();
    stack.push_back(N->Latches[i]);
    set_transition_flag(N,stack);
  }
  
  // mark the gates of the output relation
  assert(N->Outputs.size() == N->noutputs);
  clear_labels(N); // we do not need to clear labels in each iteration
  for (size_t i=0; i < N->Outputs.size();i++) {
    stack.clear();
    stack.push_back(N->Outputs[i]);
    set_output_function_flag(N,stack);
  }

} /* end of function set_trans_output_fun_flags */

/*==============================================

  F E E D S _ O N L Y _ O N E _ L A T C H

  Returns 'true' if the output of gate G
  feeds one latch (and maybe other gates
  that are not latches).

  Otherwise, returns 'false'

  ===============================================*/
bool feeds_only_one_latch(Circuit *N,Gate &G)
{ int num_of_latches = 0;
  CUBE Latches;

  for (size_t i=0; i < G.Fanout_list.size(); i++) {
    int gate_ind =  G.Fanout_list[i];
    Gate &G1 = N->get_gate(gate_ind);
    if (G1.gate_type == LATCH) {
      num_of_latches++;
      Latches.push_back(gate_ind);
    }
  }
 
  if (num_of_latches != 1) {
    std::cout << "error when checking the fanout of the gate ";
    print_name1(G.Gate_name); std::cout << "\n";
    std::cout << "total number of latches is " << num_of_latches << "\n";
    for (size_t i=0; i < Latches.size(); i++) {
      Gate &G1 = N->get_gate(Latches[i]);
      print_gate_name(G1);
      std::cout << "\n";
    }
    throw(ERROR1);
  }
  return(num_of_latches == 1);
} /* end of function feeds_only_one_latch */

/*============================================

  S E T _ F E E D S _ L A T C H _ F L A G
  
  Marks every gate whose output feeds a latch.
  Checks that no gate feeds more than one
  latch

  =============================================*/
void set_feeds_latch_flag(Circuit *N,bool ignore_errors,bool rem_dupl_opt)
{
  for (size_t i=0; i < N->Latches.size();i++)   { 
    int gate_ind = N->Latches[i];
    Gate &G = N->get_gate(gate_ind);
    int gate_ind1 = G.Fanin_list[0];
    Gate &G1 = N->get_gate(gate_ind1);
    if (!ignore_errors)
      if (!rem_dupl_opt) assert(feeds_only_one_latch(N,G1));
    G1.flags.feeds_latch = 1;
  }


} /* end of function set_feeds_latch_flag */
