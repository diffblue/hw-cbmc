/******************************************************

Module: Main

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


  Ci.init_parameters();
  read_parameters();

  try    {
    int result = get_transition_system();
    if(result!=-1) return result;

    if(make_netlist(netlist))     {
      error() << "Failed to build netlist" << eom;
      return 2;
    }
      
    if(properties.empty())   {
      error() << "no properties" << eom;
      return 1;
    }
  }

  catch(const char *error_msg)    {
    error() << error_msg << eom;
    return 1;
  }
  catch(int)    {
    return 1;
  }

  const0 = false;
  const1 = false;
  orig_names = false;
  
  // print_nodes();
  // print_var_map(std::cout);
  read_ebmc_input();
  // print_blif3("tst.blif",Ci.N);
  if (cmdline.isset("aiger")) {
    printf("converting to aiger format\n");
    Ci.print_aiger_format();
    exit(0);
  }
  
  //  printf("Constr_gates.size() = %d\n",Ci.Constr_gates.size()); 
  return(Ci.run_ic3());

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
  printf("\n");
  switch (res) {
  case 0: {
    printf("property HOLDS\n");  
    if (vac_true) {
      printf("It is vacuously true\n");
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
    printf("property FAILED\n");
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
    printf("UNDECided\n");
    ret_val = 3;
    if (print_clauses_flag) 
      print_fclauses();
    break;
  default:
    assert(false);
  }
  if (statistics) {
    printf("*********\n");
    if ((stat_data > 0) && (ret_val < 10)) print_stat();
    printf("total time is %.2f sec.\n",usrtime-usrtime0);
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

    if (verbose > 1) {
      print_bnd_sets1();     
    }
  
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
