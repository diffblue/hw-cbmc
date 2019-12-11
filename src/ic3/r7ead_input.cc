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

#include <trans-netlist/aig_prop.h>
#include <trans-netlist/instantiate_netlist.h>

#include <ebmc/ebmc_base.h>

#include "ebmc_ic3_interface.hh"

/*=====================================

       P R I N T _ V A R _ M A P

 =====================================*/
void ic3_enginet::print_var_map(std::ostream &out)
{


  printf("\n-----  Var Map ------\n");

  var_mapt &vm = netlist.var_map;
  for(var_mapt::mapt::const_iterator it=vm.map.begin();
      it!=vm.map.end(); it++)
    {
      const var_mapt::vart &var=it->second;

      for(std::size_t i=0; i<var.bits.size(); i++)
	{
	  out << "  " << it->first;
	  if(var.bits.size()!=1) out << "[" << i << "]";
	  out << "=";

	  literalt l_c=var.bits[i].current;

	  if(l_c.is_true())
	    out << "true";
	  else if(l_c.is_false())
	    out << "false";
	  else
	    {
	      if(l_c.sign()) out << "!";
	      out << l_c.var_no();
	    }
      
	  if(var.vartype==var_mapt::vart::vartypet::LATCH)
	    {
	      out << "->";
        
	      literalt l_n=var.bits[i].next;

	      if(l_n.is_true())
		out << "true";
	      else if(l_n.is_false())
		out << "false";
	      else
		{
		  if(l_n.sign()) out << "!";
		  out << l_n.var_no();
		}
	    }
       
	  out << " ";

	  switch(var.vartype)
	    {
	    case var_mapt::vart::vartypet::INPUT: out << "(input)"; break;
	    case var_mapt::vart::vartypet::LATCH: out << "(latch)"; break;
	    case var_mapt::vart::vartypet::NONDET: out << "(nondet)"; break;
	    case var_mapt::vart::vartypet::WIRE:  out << "(wire)"; break;
	    case var_mapt::vart::vartypet::OUTPUT:out << "(output)"; break;
	    case var_mapt::vart::vartypet::UNDEF: out << "(?)"; break;
	    }

	  out << '\n';
	}
    }

  out << '\n'
      << "Total no. of variable bits: " << vm.reverse_map.size() << '\n'
      << "Total no. of latch bits: " << vm.latches.size() << '\n'
      << "Total no. of nondet bits: " << vm.nondets.size() << '\n'
      << "Total no. of input bits: " << vm.inputs.size() << '\n'
      << "Total no. of output bits: " << vm.outputs.size() << '\n';

  

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

