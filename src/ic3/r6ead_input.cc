/********************************************************

Module: Converting Verilog description into an internal
        circuit presentation (part 7)

Author: Eugene Goldberg, eu.goldberg@gmail.com

********************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>

#include "Solver.h"
#include "SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

#include <solvers/prop/aig_prop.h>
#include <trans-netlist/instantiate_netlist.h>
#include "ebmc_base.h"
#include "ebmc_ic3_interface.hh"

/*==================================

    F O R M _ O R I G _ N A M E S

  ==================================*/
void ic3_enginet::form_orig_names()
{

  aigt::nodest &Nodes = netlist.nodes;
  int max_lit = (Nodes.size() << 1)+1;

  for (int i=0; i <= max_lit; i++) 
    Gn.push_back("");

  var_mapt &vm = netlist.var_map;
  for(var_mapt::mapt::const_iterator it=vm.map.begin();
      it!=vm.map.end(); it++)    {
    const var_mapt::vart &var=it->second; 
    if (var.is_wire()) continue;
    for (int j=0; j < var.bits.size(); j++) {
      literalt l_c=var.bits[j].current;
      if (l_c.is_constant()) continue;
      unsigned ind = l_c.var_no();
      irep_idt Lname = it->first;
      std::string Sname;
      short_name(Sname,Lname);
      if (var.bits.size() > 1) {
	char buf[100];
	sprintf(buf,"[%d]",j);
	Sname += buf;
      }

      assert(ind < Nodes.size());
      Gn[ind] = Sname; 
    }
  }

} /* end of function form_orig_names */


/*=================================

      P R I N T _ N O D E S 

  ===============================*/
void ic3_enginet::print_nodes()
{

  aigt::nodest &Nodes = netlist.nodes;
  for (int i=0; i <= Nodes.size(); i++) {  
    aigt::nodet &Nd = Nodes[i];
    if (Nd.is_var()) {
      printf("Nd%d: (var)\n",i);
      continue;
    }
    
    printf("Nd%d = ",i);
    print_lit2(Nd.a.var_no(),Nd.a.sign());
    printf(" & ");
    print_lit2(Nd.b.var_no(),Nd.b.sign());
    printf("\n");    

  }

} /* end of function print_nodes */


/*================================

         P R I N T _ L I T 1

  ==============================*/
void ic3_enginet::print_lit1(unsigned var,bool sign)
{
  if (sign) std::cout << "!";
  assert(var < Gn.size());
  std::cout << Gn[var];

} /* end of function print_lit1 */

/*================================

         P R I N T _ L I T 2

  ==============================*/
void ic3_enginet::print_lit2(unsigned var,bool sign)
{

  if (sign) printf("!");
  printf("v%d",var);

} /* end of function print_lit2 */

/*===============================

       S H O R T _ N A M E

  ==============================*/
void short_name(std::string &Sname,irep_idt &Lname)
{

  for (int i=Lname.size()-1; i >= 0; i--) {
    if (Lname[i] == '.') break;
    Sname.push_back(Lname[i]);
  }
  std::reverse(Sname.begin(),Sname.end());
} /* end of function short_name */

