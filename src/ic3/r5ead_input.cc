/******************************************************

Module: Reading circuit from a BLIF or AIG file
        (part 6)

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

      A S S I G N _ V A L U E

  ===============================*/
void CompInfo::assign_value()
{

  // assign value to input literals
  for (int i=0; i < Constr_ilits.size(); i++) {
    int lit = Constr_ilits[i];
    int var_ind = abs(lit)-1;
    assert(var_ind < max_num_vars);
    if (lit < 0) Var_info[var_ind].value = 0;
    else Var_info[var_ind].value = 1;
  }


  // assign value to non-input literals
  SCUBE::iterator pnt;

  for (pnt = Constr_nilits.begin(); pnt != Constr_nilits.end(); pnt++) {
    int lit = *pnt;
    int var_ind = abs(lit)-1;
    assert(var_ind < max_num_vars);
    if (lit < 0) Var_info[var_ind].value = 0;
    else Var_info[var_ind].value = 1;
  }
} /* end of function assign_value */

/*================================

  F O R M _ C O N S T R _ L I T S

  =================================*/
void CompInfo::form_constr_lits()
{

  ConstrGates::iterator pnt;

  int count = 0;
  for (pnt = Constr_gates.begin(); pnt!= Constr_gates.end(); pnt++) {
    int gate_ind = pnt->first;
    char neg_lit = pnt->second.neg_lit;
    int var = Gate_to_var[gate_ind];
    int lit;
    if (neg_lit == 0) lit = var;
    else lit = -var;

    Gate &G = N->get_gate(gate_ind);
    if (G.gate_type != LATCH) {
      if (G.gate_type == INPUT) {
	Constr_ilits.push_back(lit);
	Constr_inp_lits.insert(lit);
      }
      else { // the gate is neither latch nor combinational input
	Constr_nilits.insert(lit); 
	bool cond = (pnt->second.tran_coi || pnt->second.fun_coi);
	if (cond == false) {
	  p();
	  printf("pnt->second.tran_coi = %d\n",pnt->second.tran_coi);
	  printf("pnt->second.fun_coi = %d\n",pnt->second.fun_coi);
	  exit(100);
	}
	if (pnt->second.tran_coi)  Fun_coi_lits.push_back(lit);
	if (pnt->second.fun_coi) Tr_coi_lits.push_back(lit);}
      continue;
    }
   
    assert(G.gate_type == LATCH);
   
    Constr_ps_lits.insert(lit);
    Constr_ilits.push_back(lit);
    int nxt_var_ind = Pres_to_next[var-1];
    int nxt_var_lit;
    if (lit < 0) nxt_var_lit = -(nxt_var_ind+1);
    else nxt_var_lit = nxt_var_ind+1;
    Constr_nilits.insert(nxt_var_lit);   
  }


} /* end of function form_constr_lits */

/*=======================================

    C H E C K _ C O N S T R _ L I T S

  =======================================*/
bool CompInfo::check_constr_lits(int &fnd_lit,int lit)
{
  fnd_lit = lit;
  bool found = (Aig_clits.find(lit) != Aig_clits.end());
 
  if (!found)  {
    if (lit & 1)    fnd_lit = lit-1;
    else fnd_lit = lit +1;
    found = (Aig_clits.find(fnd_lit) != Aig_clits.end());
  }

  return(found);
} /* end of function check_constr_lits */
