/******************************************************

Module: Treating the case when a gate feeds more
        that one latch (Part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <util/invariant.h>

#include "ccircuit.hh"
#include "dnf_io.hh"

#include <algorithm>
#include <assert.h>
#include <iostream>
#include <map>
#include <queue>
#include <set>
#include <stdio.h>
#include <string.h>
#include <vector>

/*=========================================

  A D D _ O N E _ S P E C _ B U F F

  ==========================================*/
void add_one_spec_buff(Circuit *N,int ind) 
{
  int gate_ind = spec_buff_gate_ind(N,ind);
  start_spec_buff(N,gate_ind);
  add_spec_buff_cube(N,gate_ind);
  finish_spec_buff(N,gate_ind);

} /* end of function add_one_spec_buff */

/*====================================

  N A M E _ C L A S H

  This function returns 'true' if
  there is clash in names 'Root_name'
  and 'Gate_name'. A clash takes place
  if 'Gate_name' coincides with 'Root_name'
  in the first 'Root_name.size()' letters
  and the remaining letters of 'Gate_name'
  are digits
  
  ====================================*/
bool name_clash(CCUBE &Root_name,Circuit *N,int gate_ind)
{

  Gate &G = N->get_gate(gate_ind);

// special buffer gate does not have a name at this point yet
  if (G.spec_buff_ind >= 0) return(false); 


  CCUBE &Gate_name = G.Gate_name;

  if (Root_name.size() > Gate_name.size()) return(false); 

  for (size_t i=0; i < Root_name.size(); i++)
    if (Gate_name[i] != Root_name[i]) return(false);

  int count = 0;

  for (size_t i=Root_name.size(); i < Gate_name.size(); i++) {
    char symb = Gate_name[i];
    if ((symb >= '0') && (symb <= '9')) {
      count++;
      continue;}
    // non-digital symbol
    return(false);
  }
  return(count > 0); // return 'true' if all trailing symbols are digits

} /* end of function name_clash */

/*======================================

  G E N _ S P E C _ B U F F _ N A M E

  =====================================*/
void gen_spec_buff_name(Circuit *N)
{

  CCUBE &Spec_buff_name =  N->Spec_buff_name;

  Spec_buff_name.push_back('z');

  GCUBE &Gate_list = N->Gate_list;

  while (true) {
    bool clash = false;
    for (size_t i=0; i < Gate_list.size(); i++) {
      if (name_clash(Spec_buff_name,N,i)) {
	clash = true;
	Spec_buff_name.push_back('z'); // add one more letter to the name
	break;
      }
    }
    
    if (clash == false) break;
  }

} /* end of function gen_spec_buff_name */

/*========================================

  S P E C _ B U F F _ G A T E _ I N D

  =======================================*/
int spec_buff_gate_ind(Circuit *N,int ind)
{

  CCUBE fake_name;

  gen_fake_name(fake_name,ind);
  assert(N->Pin_list.find(fake_name) != N->Pin_list.end());

  int gate_ind = N->Pin_list[fake_name];

  Gate &G = N->get_gate(gate_ind);
  INVARIANT(
    G.spec_buff_ind == ind,
    "Special buffer index of gate should be equal to value of `ind`");

  return(gate_ind);

} /* end of function spec_buff_gate_ind */




