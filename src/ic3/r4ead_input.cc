/******************************************************

Module: Reading circuit from a BLIF or AIG file
        (part 5)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>

#include "ebmc_base.h"

#include "Solver.h"
#include "SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

#include "ebmc_ic3_interface.hh"
/*=========================================

      U P D _ G A T E _ C O N S T R S

  =======================================*/
void ic3_enginet::upd_gate_constrs(int node_ind,CUBE &Gate_inds) 
{
  assert(Gate_inds.size() == 3);

  aigt::nodest &Nodes = netlist.nodes;
  aigt::nodet &Nd = Nodes[node_ind];

  Ci.upd_gate_constr_tbl(Nd.a.get(),Gate_inds[0]);
  Ci.upd_gate_constr_tbl(Nd.b.get(),Gate_inds[1]);

  literalt gt_lit(node_ind,false);

  Ci.upd_gate_constr_tbl(gt_lit.get(),Gate_inds[2]);

} /* end of function upd_gate_constrs */

/*=====================================================

      U P D _ G A T E _ C O N S T R _ T B L

   Returns 

    0 if neither 'lit' nor '~lit' are constrained
    1 if 'lit' or '~lit' are constrained and 'Constr_gates'
      had no entry for 'gate_ind'
    2 if 'Constr_gates' has an entry for 'gate_ind'

  =====================================================*/
int CompInfo::upd_gate_constr_tbl(int lit,int gate_ind)
{


} /* end of function proc_lit_if_constr */

/*=====================================

   S T O R E _ C O N S T R A I N T S

  ======================================*/
void CompInfo::store_constraints()
{


} /* end of function store_constraints */

/*======================================

       F O R M _ L A T C H _ N A M E

 ======================================*/
void form_latch_name(CCUBE &Latch_name,int lit) 
{
  char Buff[MAX_NAME];
  sprintf(Buff,"l%d",lit);
  conv_to_vect(Latch_name,Buff);
} /* end of function form_latch_name */



/*===================================

        P A R S E _ S T R I N G

  returns 
   1  if Buff contains '.latch'
   0   Otherwise

  =================================*/
int parse_string(CCUBE &Buff) 
{

  if (Buff.size() == 0) return(0);
  char Command[7];

  for (int i=0; i < 6; i++) 
    Command[i] = Buff[i];
  Command[6] = 0;

  if (strcmp(Command,".latch") == 0) return(1);

  return(0);

} /* end of function parse_string */


/*===============================================

    P R I N T _ N A M E S _ O F _ L A T C H E S

  ===============================================*/
void print_names_of_latches(NamesOfLatches &Latches) 
{

  NamesOfLatches::iterator pnt;

  for (pnt = Latches.begin(); pnt != Latches.end(); pnt++) {
    CCUBE A = pnt->first;
    print_name(&A);
    printf("\n"); 
  }
} /* end of function print_names_of_latches */

/*======================================

     E B M C _ F O R M _ L A T C H E S

  =====================================*/
void ic3_enginet::ebmc_form_latches()
{

  var_mapt &vm = netlist.var_map;

  for(var_mapt::mapt::const_iterator it=vm.map.begin();
      it!=vm.map.end(); it++)    {
    const var_mapt::vart &var=it->second; 
     if (var.vartype !=var_mapt::vart::vartypet::LATCH) 
       continue;

    assert(var.bits.size() == 1);
    literalt lit =var.bits[0].current;
    Latch_val[lit.var_no()] = 2; // set the value of the latch to a don't care     
  }

  // set initial values
  bvt Ist_lits;
  gen_ist_lits(Ist_lits);
 
  for (int i=0; i < Ist_lits.size(); i++) {
    literalt &lit = Ist_lits[i];
    int var_num = lit.var_no();
    assert(Latch_val.find(var_num) != Latch_val.end());
    if (lit.sign()) Latch_val[var_num] = 0;
    else Latch_val[var_num] = 1;
  }

} /* end of function ebmc_form_latches */

/*==================================

       G E N _ I S T _ L I T S

  =================================*/
void ic3_enginet::gen_ist_lits(bvt &Ist_lits)
{

  std::set <literalt> Visited;
  assert(netlist.initial.size() == 1);
  literalt start_lit = netlist.initial[0];
  
  bvt stack;
  aigt::nodest &Nodes = netlist.nodes;
  stack.push_back(start_lit);

  while (stack.size() > 0) {

    literalt lit = stack.back();
    int var_num = lit.var_no();
    stack.pop_back();
    if (Visited.find(lit) != Visited.end()) 
      continue;
    assert(var_num < Nodes.size());
    aigt::nodet &Nd = Nodes[var_num];

    if (Nd.is_var()) {
      Ist_lits.push_back(lit);
      continue;
    }

    Visited.insert(lit);
    stack.push_back(Nd.a);
    stack.push_back(Nd.b);
  }

} /* end of function gen_ist_lits */
