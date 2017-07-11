/******************************************************

Module: Adding a new gate (Part 2)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <sstream>
#include <list>
#include <vector>
#include <set>
#include <map>
#include <string>
#include <algorithm>
#include <queue>


#include <stdio.h>
#include <assert.h>
#include "dnf_io.hh"
#include "ccircuit.hh"



/*====================================

      G E N _ F A K E _ N A M E

  ===================================*/
void gen_fake_name(CCUBE &fake_name,int ind)
{

  fake_name.clear();
  fake_name.push_back(1); // add a non-character symbol
  
  std::string Str = std::to_string(ind);

  for(size_t i=0;i < Str.size();i++) 
    fake_name.push_back(Str[i]);
    

} /* end of function gen_fake_name */



/*========================================================


   A S S I G N _ I N P U T _ P I N _ N U M B E R 2

 The function assigns a numeric lable to an input of a LATCH.
 This input is specified by 'name'. If this name has already
 been seen than a fake input equivalent to the one specified
 by 'name' is created
=========================================================*/
int assign_input_pin_number2(NamesOfLatches &Latches,Circuit *N,CCUBE &name,
                             GCUBE &gate_list)
{int pin_num;
 Gate G;

 
 std::map<CCUBE,int> &pin_list = N->Pin_list;

 bool name_exists = (pin_list.find(name) != pin_list.end());
 if (name_exists == false) {  
   init_gate_fields(G);
   pin_num = pin_list.size(); // new pin 
   pin_list[name] = pin_num;
   G.flags.active = 0;
   G.gate_type = UNDEFINED;
   Latches[name] = 1;
   gate_list.push_back(G); // add one more gate  
   return(pin_num);
 }

 int gate_ind = pin_list[name];
 Gate &G1 = N->get_gate(gate_ind);


 if ((G1.gate_type == INPUT) && (G1.inp_feeds_latch == false)) {
   G1.inp_feeds_latch = true;
   return(gate_ind);
 }



 bool latch_flag  = (Latches.find(name) != Latches.end());
 if (latch_flag && (Latches[name] == 0)) {
   Latches[name] = 1;
   return(gate_ind);
 }

 
 init_gate_fields(G);
 pin_num = pin_list.size(); // new pin 
 CCUBE fake_name;
 gen_fake_name(fake_name,N->num_spec_buffs);
 pin_list[fake_name] = pin_num;
 G.flags.active = 0;
 G.gate_type = UNDEFINED;  
 G.seed_gate = pin_list[name];
 G.spec_buff_ind = N->num_spec_buffs;
 gate_list.push_back(G);
 (N->num_spec_buffs)++;
 
 return(pin_num);

} /* end of function assign_input_pin_number2 */
