/******************************************************

Module: Reading circuit from a BLIF or AIG file
        (part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
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

/*==========================

    R E A D _ I N P U T

  =========================*/
void CompInfo::read_input(char *fname) {


  if (file_format == 'b')  blif_format_model(fname);
  else if (file_format == 'a') aig_format_model(fname);
  else assert(false); // shouldn't reach this line

  assert(N->noutputs == 1);
  assert(N->nlatches > 0);
  
  
  gen_cnfs(fname,false);
 

  num_tr_vars = find_max_var(Tr);
  num_ist_vars = find_max_var(Ist);
  num_prop_vars = find_max_var(Prop);

  int tmp = std::max(num_ist_vars,num_prop_vars);
  max_num_vars0 = std::max(tmp,num_tr_vars);
  max_num_vars = max_num_vars0 + num_prop_vars; // we need to take into account
                      // that property needs to be specified in two time frames

  build_arrays();
 
  form_max_pres_svar();

  form_constr_lits();
  add_constrs();
  
} /* end of function read_input */


/*==============================================

        F O R M _ C I R C _ F R O M _ A I G

  =============================================*/
void CompInfo::form_circ_from_aig(aiger &Aig) 
{

  if (Aig.num_outputs > 0) {
    assert(Aig.num_bad == 0);
    assert(prop_ind < Aig.num_outputs);
  }
  else {// Aig.num_outputs == 0
    assert(Aig.num_bad > 0);
    assert(prop_ind < Aig.num_bad);
  }


  N = create_circuit();
  
  const_flags = 0;
  store_constraints(Aig);
  form_inputs(N,Aig);
  int outp_lit;
  form_output(outp_lit,N,Aig);
  form_latches(N,Aig);
  
  form_gates(N,Aig);
 
  CDNF Out_names;
  form_outp_buf(Out_names,N,outp_lit);
  form_invs(N);
  form_consts(N);
 
  add_spec_buffs(N);
 
  fill_fanout_lists(N);
 
  
  
  assign_gate_type(N,Out_names,true);

  // assign topological levels and other flags
  assign_levels_from_inputs(N);
// check_levels_from_inputs(N,true);
  set_trans_output_fun_flags(N);
  set_feeds_latch_flag(N,true,true);
  assign_levels_from_outputs(N);
// check_levels_from_outputs(N,true);
 
} /* end of function form_circ_from_aig */


/*=================================

       F O R M _ T A B L E

  ================================*/
void form_table(CUBE &Table1,CUBE &Table0,int max_num_vars)
{
  Table1.assign(max_num_vars,-1);

  for (int i=0; i < Table0.size(); i++,i++) {
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
  // printf("build_arrays\n");
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
  //  printf("form_max_pres_svar\n");
  int max = -1;

  for (int i=0; i < Pres_svars.size();i++) 
    if (Pres_svars[i] > max) max = Pres_svars[i];

  max_pres_svar = max;
} /* end of function form_max_pres_svar */


/*======================================

    B L I F _ F O R M A T _ M O D E L

  ======================================*/
void CompInfo::blif_format_model(char *fname) 
{
  reader_state r;

  assert(prop_ind == 0);
  NamesOfLatches Latches; // Array will contain names of latches
  read_names_of_latches(Latches,fname);
 

  FILE *fp = fopen(fname,"r");

  if (fp ==NULL) {
    printf("file %s open failure\n",fname);
    exit(1);}
 

  r.rem_dupl_opt = true;
 
  N = read_blif(fp,Latches,r);
  fclose(fp);
} /* end of function blif_format_model */


/*=========================================

      A I G _ F O R M A T _ M O D E L

  ==========================================*/
void CompInfo::aig_format_model(char *fname) 
{

 // read AIGER model
  aiger *Aig_descr = aiger_init();
 

  FILE *fp = fopen(fname,"r");

  if (fp ==NULL) {
    printf("file %s open failure\n",fname);
    exit(1);}

  const char * Error = aiger_read_from_file(Aig_descr,fp);
  if (Error != 0) {
    std::cout << Error << std::endl;
    exit(100);}
 
  form_circ_from_aig(*Aig_descr);
  aiger_reset(Aig_descr);
  Circuit *N = this->N;

} /* end of function aig_format_model */
