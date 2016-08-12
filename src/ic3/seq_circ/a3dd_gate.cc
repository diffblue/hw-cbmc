/******************************************************

Module: Adding a new gate (Part 2)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <queue>
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "r0ead_blif.hh"


/*====================================

  G E N _ F A K E _ N A M E

  ===================================*/
void gen_fake_name(CCUBE &fake_name,int ind)
{

 
  fake_name.clear();
  fake_name.push_back(1); // add a non-character symbol
  char buf[MAX_NAME];

  sprintf(buf,"%d",ind);

  for(int i=0; ;i++) {
    if (buf[i] == 0) break;
    fake_name.push_back(buf[i]);
  }
  

} /* end of function gen_fake_name */

/*=========================================================

            A D D _ L A T C H

  The function initializes a new latch and adds it
  to the circuit N. The function returns 0 if the syntax
  of the ".latch" command is wrong. Otherwise it returns 1.
  It returns in gate_ind the numer index assigned to the
  output variable of the latch (which is also the position
  of this latch in N.gate_list)
  =============================================================*/
int add_latch(CCUBE &buf,Circuit *N,int &gate_ind)
{

  CCUBE name;

  CDNF Pin_names;
  // skip  blanks after the command text
 
  int i=str_size(".latch");
 
  skip_blanks(buf,i);

  //
  //  store the  latch pins and initial value
  //
  while (true) {
    name.clear();
    copy_name(buf,name,i);
    if (name.size() == 0)
      break;
    Pin_names.push_back(name);
    skip_blanks(buf,i);
  }
 
// command .latch should have three parameters
  if (Pin_names.size() != 3) return(0); 
 
  // process the initial value
  char c = Pin_names.back()[0];
  Pin_names.pop_back();

  int init_value;
  switch (c)
    {case '0': init_value = 0;
	break;
    case '1': init_value = 1;
      break;
    case '2': init_value = 2;
      break;
    case '3': init_value = 3;
      break;
    default:  return(0); // wrong initial latch value
    }
 
  // process the output name
  int pin_num = assign_output_pin_number(N->Pin_list,Pin_names[1],
                                         N->Gate_list,true);
  
 

  N->ngates++; // increment the number of gates 
  N->nlatches++;
  N->Latches.push_back(pin_num); // add one more latch to the list of latches
  gate_ind = pin_num;

  //  process  the  input name
  {
    pin_num = assign_input_pin_number2(N,Pin_names[0],N->Gate_list);
    Gate &G = N->get_gate(gate_ind);
    // printf("input pin_num = %d\n",pin_num);
    G.Fanin_list.push_back(pin_num); 
    if (G.gate_type == INPUT) printf("INPUT\n");
    if (N->get_gate(gate_ind).gate_type == INPUT){
//  reject circuits in which the output of a latch is also a primary input
      printf("the output of latch  ");  
      print_name1(Pin_names[1]); printf("\n");
      printf("is also an input variable\n");
      exit(1);
    }
  }
  

  /*-------------------------------------
    Form a latch node
    ---------------------------------------*/ 
 // old reference may have changed, so we need to get a fresh one
  Gate &G = N->get_gate(gate_ind); 
  
  G.ninputs = 1;
  G.func_type = BUFFER;
  G.gate_type = LATCH;
  G.level_from_inputs = 0; // initialize topological level 
  G.level_from_outputs = 0;
  G.flags.active = 1; // mark G as an active  gate
  G.flags.output = 0; 
  G.flags.transition = 0;
  G.flags.feeds_latch = 0;
  G.flags.output_function = 0;
  G.Gate_name =  Pin_names[1]; 
  G.init_value = init_value;
  G.latch_feeds_latch = false;
  return(1);
}/* end of function add_latch */


/*========================================================


  A S S I G N _ I N P U T _ P I N _ N U M B E R 2

  The function assigns a numeric lable to an input of a LATCH.
  This input is specified by 'name'. If this name has already
  been seen than a fake input equivalent to the one specified
  by 'name' is created
  =========================================================*/
int assign_input_pin_number2(Circuit *N,CCUBE &name,GCUBE &gate_list)
{int pin_num;
  Gate G;

 
  std::map<CCUBE,int> &Pin_list = N->Pin_list;

  bool name_exists = (Pin_list.find(name) != Pin_list.end());
  if (name_exists == false) {  
    init_gate_fields(G);
    pin_num = Pin_list.size(); // new pin 
    Pin_list[name] = pin_num;
    G.flags.active = 0;
    G.gate_type = UNDEFINED;
    gate_list.push_back(G); // add one more gate 
    return(pin_num);
  }

  int gate_ind = Pin_list[name];
  Gate &G1 = N->get_gate(gate_ind);

  if ((G1.gate_type == INPUT) && (G1.inp_feeds_latch == false)) {
    G1.inp_feeds_latch = true;
    return(gate_ind);
  }

  if ((G1.gate_type == LATCH) && (G1.latch_feeds_latch == false)) {
    G1.latch_feeds_latch = true;
    return(gate_ind);
  }


  init_gate_fields(G);
  pin_num = Pin_list.size(); // new pin 
  CCUBE fake_name;
  gen_fake_name(fake_name,N->num_spec_buffs);
  Pin_list[fake_name] = pin_num;
  G.flags.active = 0;
  G.gate_type = UNDEFINED;  
  G.seed_gate = Pin_list[name];
  G.spec_buff_ind = N->num_spec_buffs;
  gate_list.push_back(G);
  (N->num_spec_buffs)++;
 
  return(pin_num);

} /* end of function assign_input_pin_number2 */
