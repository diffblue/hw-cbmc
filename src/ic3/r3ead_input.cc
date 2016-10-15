/******************************************************

Module: Reading circuit from a BLIF or AIG file
        (part 4)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include "Solver.h"
#include "SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "r0ead_blif.hh"
#include "m0ic3.hh"


/*====================================

  F O R M _ G A T E _ F U N

  ==================================*/
void CompInfo::form_gate_fun(Circuit *N,int gate_ind,CUBE &Pol)
{

  assert(Pol.size() == 3);
  CUBE C;

  for (int i=0; i < Pol.size()-1; i++) {  
    if (Pol[i] == 0) C.push_back(-(i+1));
    else C.push_back((i+1));  
  }

  Gate &G = N->get_gate(gate_ind);
  G.F.push_back(C);

} /* end of function form_gate_fun */


/*============================================

  A D D _ G A T E _  O U T _ N A M E

  =============================================*/
void CompInfo::add_gate_out_name(CCUBE &Name,int lit,CUBE &Pol)
{

  unsigned lit1;
  if (lit & 1) {
    Pol.push_back(0);
    lit1 = lit-1;}
  else {
    Pol.push_back(1);
    lit1 = lit;}

  char Buff[MAX_NAME];
  sprintf(Buff,"a%d",lit1);
  conv_to_vect(Name,Buff);

} /* end of function add_gate_out_name */


/*=======================================

  A D D _ G A T E _ I N P _ N A M E

  ========================================*/
void CompInfo::add_gate_inp_name(CCUBE &Name,int lit,CUBE &Pol)
{

  if (lit <= 1) {
    if (lit == 0) {
      conv_to_vect(Name,"c0");
      const_flags = const_flags | 1;
      Pol.push_back(1);
    }
    else if  (lit == 1) {
      conv_to_vect(Name,"c1");
      const_flags = const_flags | 2;
      Pol.push_back(1);
    }
    return;
  }

  unsigned lit1;
  if (lit & 1) {
    Pol.push_back(0);
    lit1 = lit-1;}
  else {
    Pol.push_back(1);
    lit1 = lit;}

  char Buff[MAX_NAME];
  if (Inps.find(lit1) != Inps.end()) {
    sprintf(Buff,"i%d",lit1);
    conv_to_vect(Name,Buff);
  }
  else if (Lats.find(lit1) != Lats.end()) {
    sprintf(Buff,"l%d",lit1);
    conv_to_vect(Name,Buff);
  }
  else {
    sprintf(Buff,"a%d",lit1);
    conv_to_vect(Name,Buff);
  }

} /* end of function add_gate_inp_name */

/*=========================================

  F O R M _ G A T E _ P I N _ N A M E S

  =========================================*/
void CompInfo::form_gate_pin_names(CDNF &Pin_names,CUBE &Pol,
                                   aiger_and &Aig_gate)
{
  for (int i=0; i < 3; i++) {
    CCUBE Dummy;
    Pin_names.push_back(Dummy);
  }

  add_gate_inp_name(Pin_names[0],Aig_gate.rhs0,Pol);
  add_gate_inp_name(Pin_names[1],Aig_gate.rhs1,Pol);
  add_gate_out_name(Pin_names[2],Aig_gate.lhs,Pol);


} /* end of function from_gate_pin_names */

/*===============================

      F O R M _ G A T E S

  =============================*/
void CompInfo::form_gates(Circuit *N,aiger &Aig)
{

  for (int i=0; i < Aig.num_ands; i++) {
    aiger_and &Aig_gate = Aig.ands[i];
    CDNF Pin_names;
    CUBE Pol;
    form_gate_pin_names(Pin_names,Pol,Aig_gate);
    CUBE Gate_inds;
    start_new_gate(Gate_inds,N,Pin_names);
    upd_gate_constrs(Aig_gate,Gate_inds);
    form_gate_fun(N,Gate_inds.back(),Pol);
    finish_gate(N,Gate_inds.back());
  }

} /* end of function form_gates */

/*====================================

    F O R M _ O U T P _ B U F

  ===================================*/
void CompInfo::form_outp_buf(CDNF &Out_names,Circuit *N,int outp_lit)
{

  int olit = outp_lit;
  if (outp_lit > 1) 
    if (outp_lit & 1) olit--;
  

  assert(Inps.find(olit) == Inps.end());
  bool latch = false;
  if (Lats.find(olit) != Lats.end()) latch = true;

  CDNF Pin_names;
  CCUBE Dummy;
  Pin_names.push_back(Dummy);
  Pin_names.push_back(Dummy);
  char Buff[MAX_NAME];
  if (olit == 0)  sprintf(Buff,"c0");
  else if (olit == 1) sprintf(Buff,"c1");
  else  if (latch) sprintf(Buff,"l%d",olit);
  else sprintf(Buff,"a%d",olit);
  
  conv_to_vect(Pin_names[0],Buff);
  char buff[MAX_NAME];
  sprintf(buff,"p%d",prop_ind);
  conv_to_vect(Pin_names[1],buff);
  Out_names.push_back(Pin_names[1]);

  CUBE Gate_inds;
  start_new_gate(Gate_inds,N,Pin_names);
  // add cube specifying functionality
  CUBE C;
  if (outp_lit == olit) C.push_back(1);
  else C.push_back(-1);

  Gate &G = N->get_gate(Gate_inds.back());
  G.F.push_back(C);

  finish_gate(N,Gate_inds.back());

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
    finish_gate(N,Gate_inds.back());
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
    finish_gate(N,Gate_inds.back());
  }

} /* end of functin form_consts */
