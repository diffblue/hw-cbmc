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
    std::string Sname;
    short_name(Sname,Lname);      
    CCUBE K;
    conv_to_vect(K,Sname);    
    if (Ci.Cgate_names.find(K) != Ci.Cgate_names.end())  {
      literalt lit = l_c;
      if (Ci.Cgate_names[K] != l_c.sign()) lit = !l_c;
      Ci.Init_clits.insert(lit.get());
    }
  }

} /* end of function form_init_constr_lits */

