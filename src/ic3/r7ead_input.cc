/********************************************************

Module: Converting Verilog description into an internal
        circuit presentation (part 8)

Author: Eugene Goldberg, eu.goldberg@gmail.com

********************************************************/
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

#include <solvers/prop/aig_prop.h>
#include <trans-netlist/instantiate_netlist.h>
#include <ebmc/ebmc_base.h>
#include "ebmc_ic3_interface.hh"

/*=====================================

       P R I N T _ V A R _ M A P

  =====================================*/
void ic3_enginet::print_var_map()
{


  var_mapt &vm = netlist.var_map;

  for(var_mapt::mapt::const_iterator it=vm.map.begin();
      it!=vm.map.end(); it++)    {
    const var_mapt::vart &var=it->second;
    if (var.is_input()) printf("input: ");
    else if (var.is_latch()) printf("latch: ");
    else if (var.is_nondet()) printf("nondet: ");
    else if (var.is_wire()) printf("wire:" );
    else assert(false);
    
    for (size_t j=0; j < var.bits.size(); j++) {
      if (j > 0) printf(", ");
      literalt lit =var.bits[j].current;
      unsigned lit_val = lit.get();
      printf("[%zu] = %u",j,lit_val);
    }
    printf("\n");
  }
  

} /* end of function print_var_map */
/*=========================================

        A D D _ P S E U D O _ I N P S

  ==========================================*/
void ic3_enginet::add_pseudo_inps(Circuit *N)
{


  GCUBE &Gate_list = N->Gate_list;
  for (size_t i=0; i < Gate_list.size();i++) {
    Gate &G=Gate_list[i];
    if (G.flags.active) continue;
    // printf("inactive gate: ");
    // print_name1(G.Gate_name,true);

    G.func_type = BUFFER;
    G.gate_type = INPUT;
    G.flags.active = 1; // mark this input as active 
    G.flags.output = 0;
    G.flags.transition = 0;
    G.flags.output_function = 0;
    G.flags.feeds_latch = 0;
    G.level_from_inputs = 0; // set the topological level to 0
    G.inp_feeds_latch = false;
 
    //   Add it to the circuit
   
    N->Inputs.push_back(i);
    N->ninputs++; // increment the number of inputs
   
  }

} /*end of function add_pseudo_inps */

/*=========================================

 F O R M _ I N I T _ C O N S T R _ L I T S

  ==========================================*/
void ic3_enginet::form_init_constr_lits()
{

  var_mapt &vm = netlist.var_map;
  for(var_mapt::mapt::const_iterator it=vm.map.begin();
      it!=vm.map.end(); it++)    {
    const var_mapt::vart &var=it->second; 
    if (var.bits.size() != 1) continue;
    
    literalt l_c=var.bits[0].current;
    if (l_c.is_constant()) continue;
    irep_idt Lname = it->first;
    std::string Sname = short_name(Lname);
    CCUBE K;
    conv_to_vect(K,Sname);    
    if (Ci.Cgate_names.find(K) != Ci.Cgate_names.end())  {
      literalt lit = l_c;
      if (Ci.Cgate_names[K] != l_c.sign()) lit = !l_c;
      Ci.Init_clits.insert(lit.get());
    }
  }

} /* end of function form_init_constr_lits */

