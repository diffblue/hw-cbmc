/******************************************************

Module: Converting Verilog description into an internal
        circuit presentation (part 6)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>

#include <ebmc/ebmc_base.h>

#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

#include "ebmc_ic3_interface.hh"

/*================================

   B A N N E D  _ E X P R

  ================================*/
bool ic3_enginet::banned_expr(exprt &expr) {

  if(expr.id()==ID_AG ||
     expr.id()==ID_sva_always ||
     expr.id()==ID_sva_overlapped_implication ||
     expr.id()==ID_sva_non_overlapped_implication ||
     expr.id()==ID_sva_nexttime ||
     expr.id()==ID_sva_eventually ||
     expr.id()==ID_sva_until ||
     expr.id()==ID_sva_s_until ||
     expr.id()==ID_sva_until_with ||
     expr.id()==ID_sva_s_until_with)
    return(true);

  return(false);
} /* end of function expr_ident */

/*====================================

      P R I N T _ E X P R _ I D

  ==================================*/
void ic3_enginet::print_expr_id(exprt &expr)
{

  bool found = false;
  std::cout << "-------------\n";
  if(expr.id()==ID_and) {
    std::cout << "ID_and\n";
    found = true; }
  if (expr.id()==ID_or) {
    std::cout << "ID_or\n";
    found = true; }
  if (expr.id()==ID_not) {
    std::cout << "ID_not\n";
    found = true; }
  if (expr.id()==ID_implies) {
    std::cout << "ID_implies\n";
    found = true; }
  if (expr.id()==ID_AG) {
    std::cout << "ID_AG\n";
    found = true; }
  if (expr.id()==ID_sva_always){
    std::cout << "ID_sva_always\n";
    found = true; }
  if (expr.id()==ID_sva_overlapped_implication) {
    std::cout << "ID_sva_overlapped_implication\n";
    found = true; }
  if (expr.id()==ID_sva_non_overlapped_implication) {
    std::cout << "ID_sva_non_overlapped_implication\n";
    found = true; }
  if (expr.id()==ID_sva_nexttime){
    std::cout << "ID_sva_nexttime\n";
    found = true; }
  if (expr.id()==ID_sva_eventually){
    std::cout << "ID_sva_eventually\n";
    found = true; }
  if (expr.id()==ID_sva_until) {
    std::cout << "ID_sva_until\n";
    found = true;}
  if (expr.id()==ID_sva_s_until) {
    std::cout << "ID_sva_s_until\n";
    found = true;  }
  if (expr.id()==ID_sva_until_with) {
    std::cout << "ID_sva_until_with\n";
    found = true; }
  if (expr.id()==ID_sva_s_until_with) {
    std::cout << "ID_sva_s__until_with\n";
    found = true; }
 
  if (!found) {
    std::cout << "unknown expression\n";
    throw(ERROR1);
  }

  std::cout << "\n";

} /* end of function print_expr_id */

/*==========================================

      F O R M _ N E G _ O R I G _ N A M E

  ===========================================*/
void ic3_enginet::form_neg_orig_name(CCUBE &Name,literalt &next_lit)
{

  int nlit = next_lit.get();
  
  Ci.Invs.insert(nlit-1);
  form_orig_name(Name,next_lit,true);
  Name.insert(Name.begin(),'n');
  

} /* end of function form_neg_orig_name */


/*===============================
           
   F O R M _ O R I G _ N A M E

  The function returns 'true' if
  'lit' has an original name

  ===============================*/
bool ic3_enginet::form_orig_name(CCUBE &Name,literalt &lit,bool subtract)
{

  int var_num = lit.var_no();
  if (Gn[var_num].size() > 0) {
    conv_to_vect(Name,Gn[lit.var_no()]);
    return(true);
  }

  std::ostringstream Buff;
  if (subtract) Buff << "a" << lit.get()-1;
  else Buff << "a" << lit.get();
  conv_to_vect(Name,Buff.str());
  return(false);
} /* end of function form_orig_name */


/*==============================

      A S S I G N _ V A L U E

  ===============================*/
void CompInfo::assign_value()
{

  // assign value to input literals

  for (size_t i=0; i < Constr_ilits.size(); i++) {
    int lit = Constr_ilits[i];
    size_t var_ind = abs(lit)-1;
    assert(var_ind < max_num_vars);
    if (lit < 0) Var_info[var_ind].value = 0;
    else Var_info[var_ind].value = 1;
  }


  // assign value to non-input literals
  SCUBE::iterator pnt;

  for (pnt = Constr_nilits.begin(); pnt != Constr_nilits.end(); pnt++) {
    int lit = *pnt;
    size_t var_ind = abs(lit)-1;
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
	  std::cout << "pnt->second.tran_coi = " << pnt->second.tran_coi
		    << std::endl;
	  std::cout << "pnt->second.fun_coi =" << pnt->second.fun_coi
		    << std::endl;
	  throw(ERROR1);
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
  bool found = (Init_clits.find(lit) != Init_clits.end());
 
  if (!found)  {
    if (lit & 1)    fnd_lit = lit-1;
    else fnd_lit = lit +1;
    found = (Init_clits.find(fnd_lit) != Init_clits.end());
  }

  return(found);
  
} /* end of function check_constr_lits */
