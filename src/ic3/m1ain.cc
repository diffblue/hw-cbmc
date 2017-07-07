/******************************************************

Module: Main

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
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

#include <util/cmdline.h>
#include "ebmc_ic3_interface.hh"

hsh_tbl htable_lits;
long long gcount = 0;


/*=====================

       D O _ I C 3

  ====================*/
int do_ic3(const cmdlinet &cmdline,
	   ui_message_handlert &ui_message_handler)

{
  return(ic3_enginet(cmdline,ui_message_handler)());
} /* end of function do_ic3 */

/*==================================

    O P E R A T O R

   (functionall call reloading)
  =================================*/
int ic3_enginet::operator()()

{

  messaget message(ui_message_handler);
  Ci.M = &message;


  try    {
    Ci.init_parameters();
    read_parameters();
 
    int result=get_model();

    
    if(result!=-1) return result;


    if(make_netlist(netlist))     {
      Ci.M->error() << "Failed to build netlist" << Ci.M->eom;
      throw(ERROR1);
    }
  
    
    if(properties.empty())   {
      error() << "no properties" << eom;
      return ERROR1;
    }
 

  const0 = false;
  const1 = false;
  orig_names = false;
  
   
    
  read_ebmc_input();
  
  if (cmdline.isset("aiger")) {
    Ci.M->status() << "converting to aiger format" << Ci.M->eom;
    Ci.print_aiger_format();
    throw(EARLY_EXIT);
  }

  netlistt().swap(this->netlist);
  
  return(Ci.run_ic3());

  }

  

  // catch blocks
  catch(const char *error_msg)    {
    Ci.M->error() << error_msg << Ci.M->eom;
    return ERROR1;
  }
  catch(int err_num)    {
    if (err_num != EARLY_EXIT)
      Ci.M->error() << "exception number " << err_num << Ci.M->eom;
    return err_num;
  }

} /* end of function operator */

/* ======================

       R U N _ I C 3

   ====================*/
int CompInfo::run_ic3()
{
  double usrtime0=0.,systime0=0.;
  double usrtime=0.,systime=0.;
 
  
  bool ok = check_init_states();
  assert(ok);
  assign_var_type();
  assign_value();
  get_runtime (usrtime0, systime0);
  int res = mic3();
  get_runtime (usrtime, systime);  

  int ret_val;
  M->result() << M->eom;
  switch (res) {
  case 0: {
    M->result() << "property HOLDS" << M->eom;
    if (vac_true) {
      M->result() << "It is vacuously true" << M->eom;
      ret_val = 2;
      statistics = false;
      break;
    }
    if (print_inv_flag) 
      print_invariant(print_only_ind_clauses);
    if (print_clauses_flag)
      print_fclauses();
    bool ok = ver_trans_inv();
    if (ok) ret_val = 2;
    else ret_val = 12;
    break;}
  case 1: {
    M->result() << "property FAILED" << M->eom;
    form_cex();  
    if (print_cex_flag == 1)
      fprint_cex1();
    else if (print_cex_flag == 2)
      fprint_cex2();
    if (print_clauses_flag) {
      print_invariant(true);
    }
    bool ok = ver_cex();
    if (ok)  ret_val = 1;
    else ret_val = 11;
    break;}
  case 2:
    M->result() << "UNDECided" << M->eom;
    ret_val = 3;
    if (print_clauses_flag) 
      print_fclauses();
    break;
  default:
    assert(false);
  }
  if (statistics) {
    M->result() << "*********" << M->eom;
    if ((stat_data > 0) && (ret_val < 10)) print_stat();
    M->result() << std::fixed;
    M->result().precision(1);
    M->result() << "total time is " << usrtime-usrtime0 << " sec." << M->eom;
  }
  return(ret_val);
} /* end of function run_ic3 */



/*========================

       M I C 3

   Returns: 
    0 - property holds
    1 - property failed
    2 - undecided

  =======================*/
int CompInfo::mic3()
{

  check_conv_tbl(Pres_svars,Pres_to_next,true);
  check_conv_tbl(Next_svars,Next_to_pres,false);
 
  htable_lits.hsh_init(4*max_num_vars+1);
  form_bad_states();
  form_property();
  if (use_short_prop) form_short_property();
 
  ci_init();
  bool ok = init_st_satisfy_constrs();
  if (!ok) {
    vac_true = true;
    return(0); // property holds
  }
  ok = check_one_state_cex();
  if (!ok) return(1); // property does not hold

  ok = check_two_state_cex();
  if (!ok) return(1);


  if (ctg_flag) form_coi_array();
  tf_lind = 1;
 

  init_lbs_sat_solver();
  init_lgs_sat_solver();
  int ret_val = -1;
 
  while (true) {
    max_num_tfs = tf_lind;
    int res = next_time_frame();
    print_time_frame_stat();
    fflush(stdout);   
  
    if ((res == 0) || (res == 1)) {
      ret_val = res;
      goto FINISH; }

    if (res == 3) {
      ret_val = 2;
      goto FINISH;}

    assert(res == 2);
    tf_lind++;
    if (fin_tf > 0) 
      if (tf_lind > fin_tf) {
	ret_val = 2;
	goto FINISH;}
  }
  
 FINISH:
  delete_solver(Lbs_sat);
  delete_solver(Lgs_sat);
  return(ret_val);

} /* end of function mic3 */
