/******************************************************

Module: Reading circuit from a BLIF or AIG file
        (part 3)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>
#include "Solver.h"
#include "SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "r0ead_blif.hh"
#include "m0ic3.hh"

/*====================================

   F I N D _ F I L E _ F O R M A T

  ===================================*/
void CompInfo::find_file_format(char *fname)
{

  int len = strlen(fname);
  
  char rev_fname[MAX_NAME];
  assert(MAX_NAME >= len+1);
 

  // reverse file name
  int j = 0;
  for (int i=len-1; i >=0; i--) 
    rev_fname[j++] = fname[i];

  rev_fname[j] = 0;


  if (len < 4) goto ERROR;
   
  if (strncmp(rev_fname,"gia.",4) == 0) file_format = 'a';
  else {
    if (len == 4) goto ERROR;
    if (strncmp(rev_fname,"filb.",5) == 0) file_format = 'b';
    else goto ERROR;
  }

  return;

 ERROR:
  printf("wrong file extension %s\n",fname);
  exit(1);
} /* end of function find_file_format */

/*=====================================================

          S T A R T _ N E W _ G A T E

 ======================================================*/
void CompInfo::start_new_gate(CUBE &Gate_inds,Circuit *N,CDNF &Pin_names)
{

 
  // process the output name
 

  int gate_ind = assign_output_pin_number(N->Pin_list,Pin_names.back(),
                                          N->Gate_list,false);

  N->ngates++; // increment the number of gates 

  //  process  the  input names
  for (int j=0; j < Pin_names.size()-1;j++) {
    int pin_num = assign_input_pin_number1(N->Pin_list,Pin_names[j],
                                           N->Gate_list);
    Gate &G =  N->Gate_list[gate_ind];
    G.Fanin_list.push_back(pin_num); 
    Gate_inds.push_back(pin_num);  
  }

  Gate_inds.push_back(gate_ind);

 /*-------------------------------------
       Form a gate node
---------------------------------------*/ 
 // form number of inputs
 {
   Gate &G =  N->Gate_list[gate_ind];
   G.ninputs = Pin_names.size()-1;

   if (G.ninputs == 0)  {
     N->Constants.push_back(gate_ind);
     N->nconstants++;
   }
 }
 
 Gate &G =  N->Gate_list[gate_ind];
 G.gate_type = UNDEFINED;
 G.level_from_inputs = -1; // initialize topological level
 G.level_from_outputs = -1;
 G.flags.active = 1; // mark G as an active  gate
 G.flags.output = 0;
 G.flags.transition = 0;
 G.flags.output_function = 0;
 G.flags.feeds_latch = 0;
 G.Gate_name =  Pin_names.back(); 

} /* end of function start_new_gate */


/*==========================================

         F O R M _ I N V _ N A M E S 

  ===========================================*/
void CompInfo::form_inv_names(CDNF &Pin_names,int lit)
{
  
    assert ((lit & 1) == 0);
    char Buff[MAX_NAME];
    CCUBE Dummy;
    Pin_names.push_back(Dummy);
    Pin_names.push_back(Dummy);
    if (Inps.find(lit) != Inps.end()) {
      sprintf(Buff,"i%d",lit);
      conv_to_vect(Pin_names[0],Buff);
      sprintf(Buff,"ni%d",lit);
      conv_to_vect(Pin_names[1],Buff);
      return;
    }

    if (Lats.find(lit) != Lats.end()) {
      sprintf(Buff,"l%d",lit);
      conv_to_vect(Pin_names[0],Buff);
      sprintf(Buff,"nl%d",lit);
      conv_to_vect(Pin_names[1],Buff);
      return;
    }

    sprintf(Buff,"a%d",lit);
    conv_to_vect(Pin_names[0],Buff);
    sprintf(Buff,"na%d",lit);
    conv_to_vect(Pin_names[1],Buff);
   

} /* end of function form_inv_names */



/*=======================================

        F O R M _ N E X T _ S Y M B

  ======================================*/
void CompInfo::form_next_symb(CCUBE &Name,int next_lit)
{

  if (next_lit <= 1) {
    if (next_lit == 0) {
      conv_to_vect(Name,"c0");
      const_flags = const_flags | 1;
    }
    else if (next_lit == 1) {
      conv_to_vect(Name,"c1");
      const_flags = const_flags | 2;
    }
    return;
  }

  char Buff[MAX_NAME];

  if (next_lit & 1) {
    Invs.insert(next_lit-1);
    if (Inps.find(next_lit-1) != Inps.end()) 
      sprintf(Buff,"ni%d",next_lit-1);
    else  if (Lats.find(next_lit-1) != Lats.end()) 
      sprintf(Buff,"nl%d",next_lit-1);
    else sprintf(Buff,"na%d",next_lit-1);
    conv_to_vect(Name,Buff);
    return;
  }

  if (Inps.find(next_lit) != Inps.end()) sprintf(Buff,"i%d",next_lit);
  else if (Lats.find(next_lit) != Lats.end()) sprintf(Buff,"l%d",next_lit);
  else sprintf(Buff,"a%d",next_lit);

  conv_to_vect(Name,Buff);

} /* end of function form_next_symb */


/*======================================
 
   C H E C K _ O V E R L A P P I N G

  This function checks that 'Inp_vars'
  do not overlap with 'Pres_svars'

  ====================================*/
void CompInfo::check_overlapping()
{

  SCUBE S;
  
  array_to_set(S,Pres_svars);

  for (int i=0; i < Inp_vars.size(); i++) 
    assert(S.find(Inp_vars[i]) == S.end());
  

} /* end of function check_overlapping */

/*========================================

       C H E C K _ C O N V _ T B L

  =========================================*/
void CompInfo::check_conv_tbl(CUBE &Vars,CUBE &Tbl,bool pres_svars)
{

  for (int i=0; i < Vars.size(); i++)  {
    int var_ind = Vars[i]-1;
    if (Tbl[var_ind] == -1) {
      if (pres_svars) 
	printf("no match for present state variable %d\n",var_ind+1);
      else 
	printf("no match for next state variable %d\n",var_ind+1);
      exit(1);
    }
  }

} /* end of function check_conv_tbl */
