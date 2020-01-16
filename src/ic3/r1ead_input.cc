/******************************************************

Module: Converting Verilog description into an internal
        circuit presentation (part 2)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>

#include <solvers/prop/aig_prop.h>
#include <trans-netlist/instantiate_netlist.h>

#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

#include "ebmc_ic3_interface.hh"


/*====================================

      F I N D _ P R O P _ L I T

  ====================================*/
void ic3_enginet::find_prop_lit()
{

  propertyt Prop;
  bool found = find_prop(Prop);
  assert(found);

  if (Prop.expr.id()!=ID_sva_always) {
    throw("unsupported property - only SVA always is implemented");
  }

  assert(Prop.expr.operands().size()==1);

  exprt Oper = Prop.expr.op0();

  found = banned_expr(Oper);
  if (found) {
    messaget *M = Ci.M;
    M->error() << "verification of properties of this type by IC3" << M->eom;
    M->error() << "is not implemented yet" << M->eom;
    throw(ERROR1);
  }
  assert(Oper.type().id()==ID_bool);
 
  aig_prop_constraintt aig_prop(netlist);
  aig_prop.set_message_handler(get_message_handler());
    
  const namespacet ns(symbol_table);

  prop_l=instantiate_convert(aig_prop, netlist.var_map, Oper, ns,
			     get_message_handler());

 
  
  if (prop_l.is_false()) Ci.const_flags = Ci.const_flags | 1;
  else if (prop_l.is_true()) Ci.const_flags = Ci.const_flags | 2;  
  
} /* end of function find_prop_lit */


/*===================================

  F O R M _ L A T C H E D _ G A T E S

  ==================================*/
void ic3_enginet::form_latched_gates()
{

   ebmc_form_latches();

// mark latched literals

  NamesOfLatches Latches;

  var_mapt &vm = netlist.var_map;

  for(var_mapt::mapt::const_iterator it=vm.map.begin();
      it!=vm.map.end(); it++)    {
    const var_mapt::vart &var=it->second; 
    if (var.vartype !=var_mapt::vart::vartypet::LATCH) 
      continue;

    for (size_t j=0; j < var.bits.size(); j++) {
      literalt lit =var.bits[j].current;
      Ci.Lats.insert(lit.get());
      CCUBE Latch_name;
      form_latch_name(Latch_name,lit);
      Latches[Latch_name] = 1;
    }
  }

  for(var_mapt::mapt::const_iterator it=vm.map.begin();
      it!=vm.map.end(); it++)    {
    const var_mapt::vart &var=it->second; 
    if (var.vartype !=var_mapt::vart::vartypet::LATCH) 
      continue;

    for (size_t j=0; j < var.bits.size(); j++) {
      literalt lit =var.bits[j].current;
      int init_val = Latch_val[lit.var_no()];
      literalt next_lit = var.bits[j].next;    
      add_new_latch(Latches,init_val,lit,next_lit);
    }
  }

  
} /* end of function form_latched_gates */


/*==============================

        F O R M _ I N V S

  =============================*/
void ic3_enginet::form_invs()
{


  CDNF Pin_names;

  SCUBE::iterator pnt;

  SCUBE &Invs = Ci.Invs;

  Circuit *N = Ci.N;

  for (pnt = Invs.begin(); pnt != Invs.end(); pnt++) {
    int lit = *pnt;
    Pin_names.clear();
    form_inv_names(Pin_names,lit);
    CUBE Gate_inds;
    Ci.start_new_gate(Gate_inds,N,Pin_names);
    CUBE C;
    C.push_back(-1);
    Gate &G = N->get_gate(Gate_inds.back());
    G.F.push_back(C);

    finish_gate(N,Gate_inds.back(),*Ci.M);
  }

} /* end of function form_invs */

/*===================================

        A D D _ N E W _ L A T C H

   This function is similar to
   'add_latch' of file 
   'seq_circ/a3dd_gate.cc'

  ====================================*/
void ic3_enginet::add_new_latch(NamesOfLatches &Latches, int init_val,
				literalt &pres_lit,literalt &next_lit)
{


  Circuit *N = Ci.N;

  // process the output name
  CCUBE Latch_name;
  form_latch_name(Latch_name,pres_lit); 
 
 
  int pin_num = assign_output_pin_number(N->Pin_list,Latch_name,
					 N->Gate_list,true,*Ci.M);
  Ci.upd_gate_constr_tbl(pres_lit.get(),pin_num);
 
 

  N->ngates++; // increment the number of gates 
  N->nlatches++;
  N->Latches.push_back(pin_num); // add one more latch to the list of latches
  int gate_ind = pin_num;

  CCUBE Next_name;

  form_next_symb(Next_name,next_lit);
  //  process  the  input name
  {
    pin_num = assign_input_pin_number2(Latches,N,Next_name,N->Gate_list);
    if (next_lit.sign() == 0)
      Ci.upd_gate_constr_tbl(next_lit.get(),pin_num);

    Gate &G = N->get_gate(gate_ind);   
    G.Fanin_list.push_back(pin_num); 

// we don't accept files in which the output of a latch is also a primary input
    if (G.gate_type == INPUT){
      messaget *M = Ci.M;
      M->error() << "the output of latch  ";
      M->error() << cvect_to_str(Latch_name) << M->eom;
      M->error() << "is also an input variable" << M->eom;
      throw(ERROR1);
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
  G.init_value = init_val;
 
} /* end of function add_new_latch */


/*===============================

     C O N V _ T O _ V E C T

  =============================*/
void conv_to_vect(CCUBE &Name1,const char *Name0)
{
  Name1.clear();
  for (size_t i=0; Name0[i]!=0; i++)
    Name1.push_back(Name0[i]);
} /* end of function conv_to_vect */


/*===============================

     C O N V _ T O _ V E C T

  =============================*/
CCUBE conv_to_vect(std::string &Name)
{

  CCUBE V(Name.begin(),Name.end());
  return(V);  

} /* end of function conv_to_vect */

/*===============================

     C O N V _ T O _ V E C T

  =============================*/
CCUBE conv_to_vect(const std::string &Name)
{
 
  CCUBE V(Name.begin(),Name.end());
  return(V);  

} /* end of function conv_to_vect */

