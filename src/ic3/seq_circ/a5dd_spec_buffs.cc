/******************************************************

Module: Treating the case when a gate feeds more
        that one latch (Part 2)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <sstream>
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


/*===================================

    F I N I S H _ S P E C _ B U F F 

  ==================================*/
void finish_spec_buff(Circuit *N,int gate_ind,messaget &M)
{

  Gate &G = N->get_gate(gate_ind);

  G.func_type = BUFFER;

  DNF &F = G.F;
  DNF &R = G.R;

  if ((F.size()+ R.size()) != 1) {
    M.error() << "wrong buffer " << M.eom;
    M.error() << cvect_to_str(G.Gate_name) << M.eom;
    throw(ERROR1);
  }

  assert(F.size() == 1);

  set_input_polarity(F[0],G);
  G.Polarity.push_back(0); // direct output   

} /* end of function finish_spec_buff */

/*============================================

     A D D _ S P E C _ B U F F _ C U B E

  =============================================*/
void add_spec_buff_cube(Circuit *N,int gate_ind)
{

  Gate &G = N->get_gate(gate_ind);
  assert(G.F.size() == 0);
  assert(G.R.size() == 0);
  CUBE C;
  C.push_back(1);
  G.F.push_back(C);

} /* end of function add_spec_buff_cube */

/*======================================

      F O R M _ F A N I N _ L I S T

  ======================================*/
void form_fanin_list(Circuit *N,int gate_ind)
{
  Gate &G = N->get_gate(gate_ind);

  G.ninputs = 1;
  CUBE &Fanin_list = G.Fanin_list;

  Fanin_list.clear();

  assert(G.seed_gate >= 0);

  Fanin_list.push_back(G.seed_gate);


} /* end of function form_fanin_list */


/*========================================

       F O R M _ O U T P U T _ N A M E

  =========================================*/
void form_output_name(CCUBE &Name,Circuit *N,int gate_ind)
{
  Name =  N->Spec_buff_name;

  
  Gate &G = N->get_gate(gate_ind);

  assert(G.spec_buff_ind >= 0);

  std::string Str = std::to_string(G.spec_buff_ind);

  for(size_t i=0;i < Str.size();i++) 
    Name.push_back(Str[i]);

} /* end of function form_output_name */

/*==================================

  S T A R T _ S P E C _ B U F F

  =================================*/
void start_spec_buff(Circuit *N,int gate_ind)
{


  // form the right output name
  CCUBE Name;
  form_output_name(Name,N,gate_ind);

  // form the list of fanin gates
  form_fanin_list(N,gate_ind);

  Gate &G =  N->Gate_list[gate_ind];
  G.gate_type = UNDEFINED;
  G.level_from_inputs = -1; // initialize topological level
  G.level_from_outputs = -1;
  G.flags.active = 1; // mark G as an active  gate
  G.flags.output = 0;
  G.flags.transition = 0;
  G.flags.output_function = 0;
  G.flags.feeds_latch = 0;
  G.Gate_name =  Name; 

} /* end of function start_spec_buff */


/*==================================

  A D D _ S P E C _ B U F F S

  =================================*/
void add_spec_buffs(Circuit *N,messaget &M) 
{

  if (N->num_spec_buffs == 0) return;

  gen_spec_buff_name(N);

  for (int i=0; i < N->num_spec_buffs; i++) 
    add_one_spec_buff(N,i,M);

} /* end of function add_spec_buffs */

