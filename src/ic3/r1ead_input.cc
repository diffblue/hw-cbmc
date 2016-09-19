/******************************************************

Module: Reading circuit from a BLIF or AIG file
        (part 2)

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


/*==============================

        F O R M _ I N V S

  =============================*/
void CompInfo::form_invs(Circuit *N)
{



  CDNF Pin_names;

  SCUBE::iterator pnt;

  for (pnt = Invs.begin(); pnt != Invs.end(); pnt++) {
    int lit = *pnt;
    Pin_names.clear();
    form_inv_names(Pin_names,lit);
    int gate_ind = start_new_gate(N,Pin_names);
    CUBE C;
    C.push_back(-1);
    Gate &G = N->get_gate(gate_ind);
    G.F.push_back(C);

    finish_gate(N,gate_ind);
  }

} /* end of function form_invs */

/*===================================

        A D D _ N E W _ L A T C H

   This function is similar to
   'add_latch' of file 
   'seq_circ/a3dd_gate.cc'

  ====================================*/
void CompInfo::add_new_latch(NamesOfLatches &Latches,Circuit *N,aiger_symbol &S)
{

  int init_value;

  switch (S.reset) {
  case 0:
  case 1:
    init_value = S.reset;
    break;
  default:
    assert(S.reset == S.lit);
    init_value = 2;
    break;
  }

 // process the output name
  CCUBE Latch_name;
  form_latch_name(Latch_name,S); 
 
 
  int pin_num = assign_output_pin_number(N->Pin_list,Latch_name,N->Gate_list,true);
 
 

  N->ngates++; // increment the number of gates 
  N->nlatches++;
  N->Latches.push_back(pin_num); // add one more latch to the list of latches
  int gate_ind = pin_num;

  CCUBE Next_name;

  form_next_symb(Next_name,S.next);
  //  process  the  input name
  {
    pin_num = assign_input_pin_number2(Latches,N,Next_name,N->Gate_list);

    Gate &G = N->get_gate(gate_ind);   
    G.Fanin_list.push_back(pin_num); 
    if (G.gate_type == INPUT) printf("INPUT\n");
    if (N->get_gate(gate_ind).gate_type == INPUT){
// we don't accept files in which the output of a latch is also a primary input
      printf("the output of latch  "); 
      print_name(&Latch_name); printf("\n");
      printf("is also an input variable\n");
      exit(1);
    }
  }
  

  /*-------------------------------------
    Form a latch node
    ---------------------------------------*/ 
 
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
  G.Gate_name =  Latch_name; 
  G.init_value = init_value;
  
} /* end of function add_new_latch */

/*===================================

       F O R M _ L A T C H E S

  ==================================*/
void CompInfo::form_latches(Circuit *N,aiger &Aig)
{


// mark latched literal

  NamesOfLatches Latches;

  for (int i=0; i < Aig.num_latches; i++) {
    Lats.insert(Aig.latches[i].lit);
    CCUBE Latch_name;
    form_latch_name(Latch_name,Aig.latches[i]);
    Latches[Latch_name] = 1;
  }

  for (int i=0; i < Aig.num_latches; i++) 
    add_new_latch(Latches,N,Aig.latches[i]);
  
  

} /* end of function form_latches */

/*=============================

  F O R M _ O U T P U T

  =============================*/
void CompInfo::form_output(int &outp_lit,Circuit *N,aiger &Aig)
{

  if (Aig.num_bad == 0) outp_lit = Aig.outputs[0].lit;
  else  outp_lit = Aig.bad[0].lit;

  if (outp_lit <= 1) {
    assert(outp_lit >= 0);
    if (outp_lit == 0) const_flags = const_flags | 1;
    else if (outp_lit == 1) const_flags = const_flags | 2;
  }

} /* end of function form_output */



/*===================================

        F O R M _ I N P U T S

====================================*/
void CompInfo::form_inputs(Circuit *N,aiger &Aig)
{

 for (int i=0; i < Aig.num_inputs; i++) {
    int lit = Aig.inputs[i].lit;
    char Inp_name[MAX_NAME];
    sprintf(Inp_name,"i%d",lit);
    CCUBE Name;
    conv_to_vect(Name,Inp_name);
    Inps.insert(lit);
    add_input(Name,N,N->ninputs);
  }
  

} /* end of function form_inputs */

/*===============================

     C O N V _ T O _ V E C T

  =============================*/
void conv_to_vect(CCUBE &Name1,const char *Name0)
{

  Name1.clear();
  for (int i=0; ;i++) {
    if (Name0[i] == 0) break;
    Name1.push_back(Name0[i]);
  }


} /* end of function conv_to_vect */
