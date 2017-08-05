/******************************************************

Module: Converting Verilog description into an internal
        circuit presentation (part 4)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>

#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

#include "ebmc_ic3_interface.hh"
/*====================================

     F O R M _ G A T E _ F U N

  ==================================*/
void CompInfo::form_gate_fun(Circuit *N,int gate_ind,CUBE &Pol)
{

  assert(Pol.size() == 3);
  CUBE C;

  for (size_t i=0; i < Pol.size()-1; i++) {  
    if (Pol[i] == 0) C.push_back(-(i+1));
    else C.push_back((i+1));  
  }

  Gate &G = N->get_gate(gate_ind);
  G.F.push_back(C);

} /* end of function form_gate_fun */


/*======================================

  A D D _ G A T E _  O U T _ N A M E

  =====================================*/
void ic3_enginet::add_gate_out_name(CCUBE &Name,literalt &lit,CUBE &Pol)
{

  unsigned lit1;
  unsigned lit_val = lit.get();
  if (lit.sign()) {
    Pol.push_back(0);
    lit1 = lit_val-1;}
  else {
    Pol.push_back(1);
    lit1 = lit_val;}

  if (orig_names) {
    form_orig_name(Name,lit);
    return;
  }

  std::string Str_name("a" + std::to_string(lit1));
  Name = conv_to_vect(Str_name);

} /* end of function add_gate_out_name */

/*=======================================

  A D D _ G A T E _ I N P _ N A M E

  ========================================*/
void ic3_enginet::add_gate_inp_name(CCUBE &Name,literalt &lit,CUBE &Pol)
{

  if (lit.is_constant()) {
    if (lit.is_false()) {
      conv_to_vect(Name,"c0");
      Ci.const_flags = Ci.const_flags | 1;
      Pol.push_back(1);
    }
    else {
      assert(lit.is_true());
      conv_to_vect(Name,"c1");
      Ci.const_flags = Ci.const_flags | 2;
      Pol.push_back(1);
    }
    return;
  }
  
  unsigned lit_val = lit.get();
  unsigned lit1;
  if (lit.sign()) {
    Pol.push_back(0);
    lit1 = lit_val-1;}
  else {
    Pol.push_back(1);
    lit1 = lit_val;}

  if (orig_names) {
    form_orig_name(Name,lit,lit.sign());
    return;
  }

 
  std::string Str_name;
  if (Ci.Inps.find(lit1) != Ci.Inps.end()) {
    Str_name = "i" + std::to_string(lit1);
    Name = conv_to_vect(Str_name);
  }
  else if (Ci.Lats.find(lit1) != Ci.Lats.end()) {
    Str_name = "l" + std::to_string(lit1);
    Name = conv_to_vect(Str_name);
  }
  else {
    Str_name = "a" + std::to_string(lit1);
    Name = conv_to_vect(Str_name);
  }

} /* end of function add_gate_inp_name */


/*=========================================

  F O R M _ G A T E _ P I N _ N A M E S

  =========================================*/
void ic3_enginet::form_gate_pin_names(CDNF &Pin_names,CUBE &Pol,
                                    int node_ind)
{
  for (int i=0; i < 3; i++) {
    CCUBE Dummy;
    Pin_names.push_back(Dummy);
  }

  aigt::nodest &Nodes = netlist.nodes;
  aigt::nodet &Nd = Nodes[node_ind];
 

  add_gate_inp_name(Pin_names[0],Nd.a,Pol);
  add_gate_inp_name(Pin_names[1],Nd.b,Pol);

  literalt gt_lit(node_ind,false);

  add_gate_out_name(Pin_names[2],gt_lit,Pol);
  
} /* end of function from_gate_pin_names */

/*===============================

      F O R M _ G A T E S

  =============================*/
void ic3_enginet::form_gates()
{

  Circuit *N = Ci.N;
  aigt::nodest &Nodes = netlist.nodes;

  for (size_t i=0; i <  Nodes.size(); i++) {  
    aigt::nodet &Nd = Nodes[i];
    if (Nd.is_var()) {   
      continue;
    }
    CDNF Pin_names;
    CUBE Pol;    
    form_gate_pin_names(Pin_names,Pol,i);
    CUBE Gate_inds;
    Ci.start_new_gate(Gate_inds,N,Pin_names);
    upd_gate_constrs(i,Gate_inds);
    Ci.form_gate_fun(N,Gate_inds.back(),Pol);
    finish_gate(N,Gate_inds.back(),*Ci.M);
  }
  

} /* end of function form_gates */

/*====================================

    F O R M _ O U T P _ B U F

  ===================================*/
void ic3_enginet::form_outp_buf(CDNF &Out_names,literalt &prop_lit,
                                std::string &Prop_name)
{

 
  unsigned olit = prop_lit.get();
 
  // std::cout << "olit " << olit << "\n";

  Ci.const_false_prop = false;
  Ci.const_true_prop = false;
  
  if (prop_lit.is_constant() == 0)
    if (prop_lit.sign()) 
       olit--;

  assert(Ci.Inps.find(olit) == Ci.Inps.end());
  bool latch = false;
  if (Ci.Lats.find(olit) != Ci.Lats.end()) latch = true;

  CDNF Pin_names;
  CCUBE Dummy;
  Pin_names.push_back(Dummy);
  Pin_names.push_back(Dummy);

  std::string Str_name;
 
  if (prop_lit.is_false())  {
    Ci.const_false_prop = true;
    conv_to_vect(Pin_names[0],"c0");
    goto NEXT;  }
  if (prop_lit.is_true()) {
    Ci.const_true_prop = true;
    conv_to_vect(Pin_names[0],"c1");
    goto NEXT;
  }


  if (orig_names) 
    form_orig_name(Pin_names[0],prop_lit,prop_lit.sign());
  else {
    if (latch)
      Str_name = "l" + std::to_string(olit);
    else
      Str_name = "a" + std::to_string(olit);
    Pin_names[0] = conv_to_vect(Str_name);
  }

 NEXT:

  print_name1(Pin_names[0]); printf("\n");
  Pin_names[1] = conv_to_vect(Prop_name);
  Out_names.push_back(Pin_names[1]);

  Circuit *N = Ci.N;
  CUBE Gate_inds;
  Ci.start_new_gate(Gate_inds,N,Pin_names);
  // add cube specifying functionality
  CUBE C;
  // making the buffer an invertor
  if (prop_lit.is_constant()) C.push_back(-1);
  else 
    if (prop_lit.sign()) C.push_back(1);
    else C.push_back(-1);

  Gate &G = N->get_gate(Gate_inds.back());
  G.F.push_back(C);

  finish_gate(N,Gate_inds.back(),*Ci.M);

} /* end of function form_outp_buf */

/*===================================

        F O R M _ C O N S T S

  ====================================*/
void CompInfo::form_consts(Circuit *N)
{
   
  if (const_flags & 1) {  
    CCUBE Dummy; 
    CDNF Pin_names;
    Pin_names.push_back(Dummy);
    conv_to_vect(Pin_names[0],"c0");
    CUBE Gate_inds;
    start_new_gate(Gate_inds,N,Pin_names);
    finish_gate(N,Gate_inds.back(),*M);
  }

  if (const_flags & 2) {
    CCUBE Dummy;
    CDNF Pin_names;
    Pin_names.push_back(Dummy);
    conv_to_vect(Pin_names[0],"c1");
    CUBE Gate_inds;
    start_new_gate(Gate_inds,N,Pin_names);
    CUBE C;
    Gate &G = N->get_gate(Gate_inds.back());
    G.F.push_back(C);
    finish_gate(N,Gate_inds.back(),*M);
  }

} /* end of functin form_consts */
