/******************************************************

Module: Converting Verilog description into an internal
        circuit presentation (part 3)

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


/*=====================================================

          S T A R T _ N E W _ G A T E

 ======================================================*/
void CompInfo::start_new_gate(CUBE &Gate_inds,Circuit *N,CDNF &Pin_names)
{

 
  // process the output name
 

  int gate_ind = assign_output_pin_number(N->Pin_list,Pin_names.back(),
                                          N->Gate_list,false,*M);

  N->ngates++; // increment the number of gates 

  //  process  the  input names
  for (size_t j=0; j < Pin_names.size()-1;j++) {
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
void ic3_enginet::form_inv_names(CDNF &Pin_names,int lit)
{
  
  assert ((lit & 1) == 0);
  
  CCUBE Dummy;
  Pin_names.push_back(Dummy);
  Pin_names.push_back(Dummy);
  if (orig_names) {
    literalt Lit = literalt(lit >> 1,true);
    form_orig_name(Pin_names[0],Lit,true); 
    Pin_names[1] = Pin_names[0];
    Pin_names[1].insert(Pin_names[1].begin(),'n');
    return;
  }

  
  SCUBE &Inps = Ci.Inps;

	
  if (Inps.find(lit) != Inps.end()) {
    {
      std::string Name = "i" + std::to_string(lit);
      conv_to_vect(Pin_names[0],Name);
   
      Name = "ni" + std::to_string(lit);
      conv_to_vect(Pin_names[1],Name);
    }
    return;
  }

  SCUBE &Lats = Ci.Lats;
  if (Lats.find(lit) != Lats.end()) {
    {  
      std::string Name = "l" + std::to_string(lit);
      conv_to_vect(Pin_names[0],Name);
  
      Name = "nl" + std::to_string(lit);
      conv_to_vect(Pin_names[1],Name);
    }
    return;
  }


  std::string Name = "a" + std::to_string(lit);
  conv_to_vect(Pin_names[0],Name);
  Name = "na" + std::to_string(lit);
  conv_to_vect(Pin_names[1],Name);

   

} /* end of function form_inv_names */



/*=======================================

        F O R M _ N E X T _ S Y M B

  ======================================*/
void ic3_enginet::form_next_symb(CCUBE &Name,literalt &next_lit)
{

  if (next_lit.is_constant()) {
    if (next_lit.is_false()) {
      conv_to_vect(Name,"c0");
      Ci.const_flags = Ci.const_flags | 1;
    }
    else {
      assert(next_lit.is_true());
      conv_to_vect(Name,"c1");
      Ci.const_flags = Ci.const_flags | 2;
    }
    return;
  }


  
  
  int nlit;
 

  nlit = next_lit.get();

 
  std::string Str_name;
  if (next_lit.sign()) {   
    if (orig_names) {
      form_neg_orig_name(Name,next_lit);
      return;}
    Ci.Invs.insert(nlit-1);
    if (Ci.Inps.find(nlit-1) != Ci.Inps.end())
      Str_name = "ni" + std::to_string(nlit-1);
    else  if (Ci.Lats.find(nlit-1) != Ci.Lats.end())
      Str_name = "nl" + std::to_string(nlit-1);
    else 
      Str_name = "na" + std::to_string(nlit-1);
    conv_to_vect(Name,Str_name);
    return;
  }
 


  if (orig_names) {
    form_orig_name(Name,next_lit);
    return;
  }



  if (Ci.Inps.find(nlit) != Ci.Inps.end())
    Str_name = "i" + std::to_string(nlit);
  else if (Ci.Lats.find(nlit) != Ci.Lats.end())
    Str_name = "l" + std::to_string(nlit);
  else
    Str_name = "a" + std::to_string(nlit);
  conv_to_vect(Name,Str_name);
  

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

  for (size_t i=0; i < Inp_vars.size(); i++) 
    assert(S.find(Inp_vars[i]) == S.end());
  

} /* end of function check_overlapping */

/*========================================

       C H E C K _ C O N V _ T B L

  =========================================*/
void CompInfo::check_conv_tbl(CUBE &Vars,CUBE &Tbl,bool pres_svars)
{

  for (size_t i=0; i < Vars.size(); i++)  {
    int var_ind = Vars[i]-1;
    if (Tbl[var_ind] == -1) {
      if (pres_svars) 
	M->error() << "no match for present state variable " << var_ind+1
		  << M->eom;
      else 
	M->error() << "no match for next state variable "<< var_ind+1
		  << M->eom;
      throw(ERROR1);
    }
  }

} /* end of function check_conv_tbl */
