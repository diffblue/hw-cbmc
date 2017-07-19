/******************************************************

Module: Converting Verilog description into an internal
        circuit presentation (part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"
#include <util/cmdline.h>
#include "ebmc_ic3_interface.hh"

/*=================================

    R E A D _ E B M C _ I N P U T

  ===============================*/
void ic3_enginet::read_ebmc_input(std::vector <literalt> &All_plits)
{

  store_constraints(cmdline.args[0]);
 
  form_orig_names();
 
  form_circ_from_ebmc(All_plits);

  if(cmdline.isset("aiger") == 0)
    assert(Ci.N->noutputs == 1);
  assert(Ci.N->nlatches > 0);

  Ci.order_gates();
  std::string empty;
  Ci.gen_cnfs(empty.c_str(), false);

  Ci.form_var_nums();
 

  Ci.build_arrays();
 
  Ci.form_max_pres_svar();

  Ci.form_constr_lits();
  Ci.add_constrs();
  
} /* end of function read_ebmc_input */

/*==============================================

        F O R M _ C I R C _ F R O M _ E B M C

  =============================================*/
void ic3_enginet::form_circ_from_ebmc(std::vector <literalt> &Plits) 
{

  Circuit *N = create_circuit();
  Ci.N = N;
  
  Ci.const_flags = 0;


  form_inputs();


  std::vector<std::string> Pnames;
  if(cmdline.isset("aiger")) all_prop_lits(Plits,Pnames);
  else  find_prop_lit();
 
 
  
  form_latched_gates();

  form_gates();
 
  CDNF Out_names;
  if (cmdline.isset("aiger") == 0) 
    form_outp_buf(Out_names,prop_l,Ci.prop_name);
  else {
    for (size_t i = 0; i < Plits.size(); i++) {
      form_outp_buf(Out_names,Plits[i],Pnames[i]);
      printf("output name ");
      print_name1(Out_names.back(),true);
    }
  }
  form_invs();
  Ci.form_consts(N);
 
  add_spec_buffs(N,*Ci.M);

  add_pseudo_inps(N);
 
  fill_fanout_lists(N,*Ci.M);
  assign_gate_type(N,Out_names,true,*Ci.M);
  //   assign topological levels and other flags
  assign_levels_from_inputs(N,*Ci.M);
  // check_levels_from_inputs(N,true);
  set_trans_output_fun_flags(N);
  set_feeds_latch_flag(N,true,true,*Ci.M);
  assign_levels_from_outputs(N,*Ci.M);
  // check_levels_from_outputs(N,true);

} /* end of function form_circ_from_ebmc */

/*===================================

        F O R M _ I N P U T S

====================================*/
void ic3_enginet::form_inputs()
{

  var_mapt &vm = netlist.var_map;
  Circuit *N = Ci.N;

  for(var_mapt::mapt::const_iterator it=vm.map.begin();
      it!=vm.map.end(); it++)    {
    const var_mapt::vart &var=it->second;
    if (var.is_input() == false) continue;
    for (size_t j=0; j < var.bits.size(); j++) {  
      literalt lit =var.bits[j].current;
      int lit_val = lit.get();
      CCUBE Name;
      if (orig_names) {
	bool ok = form_orig_name(Name,lit);
	assert(ok);}      
      else {
	std::string Inp_name("i" + std::to_string(lit_val));
        Name = conv_to_vect(Inp_name);
      }
      Ci.Inps.insert(lit_val);
      add_input(Name,N,N->ninputs);
      Ci.upd_gate_constr_tbl(lit_val,N->ninputs);
    }
  }
  

} /* end of function form_inputs */


/*=================================

       F O R M _ T A B L E

  ================================*/
void form_table(CUBE &Table1,CUBE &Table0,int max_num_vars)
{
  Table1.assign(max_num_vars,-1);

  for (size_t i=0; i < Table0.size(); i++,i++) {
    int var_ind_from = Table0[i]-1;
    int var_ind_to = Table0[i+1]-1;
    assert(var_ind_from < max_num_vars);
    assert(var_ind_to < max_num_vars);
    Table1[var_ind_from] = var_ind_to;
  }

} /* end of function form_table */

/*=============================

    B U I L D _ A R R A Y S

  ============================*/
void CompInfo::build_arrays() {

  form_pres_state_vars();  
  form_next_state_vars();
  form_inp_vars(); 
  form_pres_to_next_conv();
  form_next_to_pres_conv();
} /* end of function build_arrays */
 
/*=====================================

  F O R M _ M A X _ P R E S _ S V A R

  ======================================*/
void CompInfo::form_max_pres_svar() {

  int max = -1;

  for (size_t i=0; i < Pres_svars.size();i++) 
    if (Pres_svars[i] > max) max = Pres_svars[i];

  max_pres_svar = max;
} /* end of function form_max_pres_svar */

/*===================================

      F O R M _ V A R _ N U M S

  ==================================*/
void CompInfo::form_var_nums()
{
  num_tr_vars = find_max_var(Tr);
  num_ist_vars = find_max_var(Ist);
  num_prop_vars = find_max_var(Prop);

  int tmp = std::max(num_ist_vars,num_prop_vars);
  max_num_vars0 = std::max(tmp,num_tr_vars);
  max_num_vars = max_num_vars0 + num_prop_vars; // we need to take into account
  // that property needs to be specified in two time frames
} /* end of function form_var_nums */

/*================================================

   A D D _ V E R I L O G _ C O N V _ C O N S T R S

  ================================================*/
void ic3_enginet::add_verilog_conv_constrs()
{

  for(literalt lit : netlist.constraints) {
    if (lit.is_constant()) continue;   
     Ci.Init_clits.insert(lit.get());
  }


} /* end of function add_verlig_conv_constrs */
