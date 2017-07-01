/******************************************************

Module: Adding a new gate (Part 1)

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


/*==========================================================


  A S S I G N _ I N P U T _ P I N _ N U M B E R 1

  The function assigns a numeric lable to an input of a gate.
  The function either puts name into the map pin_list
  (if it is new) and returns its key, or just returns
  the key (name is already in  pin_list).  If 'name' is new
  a new gate is added to gate_list
  =========================================================*/
int assign_input_pin_number1(std::map<CCUBE,int> &pin_list,
			     CCUBE &name,GCUBE &gate_list)
{int pin_num;
  Gate G;

  if (pin_list.find(name) == pin_list.end()) {
    init_gate_fields(G);
    pin_num = pin_list.size(); // new pin 
    pin_list[name] = pin_num;
    G.flags.active = 0;
    G.gate_type = UNDEFINED;
    G.Gate_name = name;
    gate_list.push_back(G); // add one more gate 
  }
  else /* an 'old' pin */
    pin_num=pin_list[name]; // add to input list the current gate input      
     
  return(pin_num);

} /* end of function assign_input_pin_number1 */

/*========================================================


  A S S I G N _ O U T P U T _ P I N _ N U M B E R

  The function assigns a numeric lable to the output of a
  gate. The function either puts name into the map pin_list
  (if it is new) and returns its key, or just returns
  the key (name is already in  pin_list).  If 'name' is new
  a new gate is added to gate_list
  =========================================================*/
int assign_output_pin_number(std::map<CCUBE,int> &pin_list,
			     CCUBE &name,GCUBE &gate_list,bool latch)
{int pin_num;
  Gate G;


  if (pin_list.find(name) == pin_list.end()) {  
    init_gate_fields(G);
    pin_num = pin_list.size(); // new pin 
    pin_list[name] = pin_num;
    G.flags.active = 0;
    G.gate_type = UNDEFINED;   
    if (latch) 
      G.gate_type = LATCH;
    gate_list.push_back(G); // add one more gate 
  }
  else { /* an 'old' pin */
    pin_num=pin_list[name]; // add to input list the current gate input      
    if (gate_list[pin_num].flags.active == 1) {
      std::cout << "two gates have the same name "; 
      print_name1(name); 
      std::cout << "\n";
      throw(ERROR1);   
    }
  }
  return(pin_num);

} /* end of function assign_output_pin_number */



/*==========================================

  A D D _ I N P U T

  The function adds a new input to circuit N

  ===========================================*/
void add_input(CCUBE &name,Circuit *N,int inp_gate_num)
{Gate I;

  init_gate_fields(I);

  //    Form an input node

  I.func_type = BUFFER;
  I.gate_type = INPUT;
  I.flags.active = 1; // mark this input as active 
  I.flags.output = 0;
  I.flags.transition = 0;
  I.flags.output_function = 0;
  I.flags.feeds_latch = 0;
  I.level_from_inputs = 0; // set the topological level to 0
  I.Gate_name = name;
  I.inp_feeds_latch = false;

 
  //   Add it to the circuit
   
  N->Inputs.push_back(inp_gate_num);
  N->ninputs++; // increment the number of inputs
  N->Gate_list.push_back(I); // add input 
  N->Pin_list[name] = inp_gate_num;
 

}/* end of function add_input */
