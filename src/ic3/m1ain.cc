/******************************************************

Module: Main

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
#include "m0ic3.hh"


hsh_tbl htable_lits;
long long gcount = 0;


/*========================

  M I C 3

  Returns: 
  0 - property holds
  1 - property failed
  2 - undecided

  =======================*/
int CompInfo::mic3()
{

  htable_lits.hsh_init(4*max_num_vars+1);
  form_bad_states();
  form_property();
  if (use_short_prop) form_short_property();
 
  ci_init();
  bool ok = check_one_state_cex();
  if (!ok) return(1);

  ok = check_two_state_cex();
  if (!ok) return(1);

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

/*===================

  M A I N

  ====================*/
int  main(int argc,char *argv[])
{
  CompInfo Ci;
  double usrtime0=0.,systime0=0.;
  double usrtime=0.,systime=0.;

  if (argc == 1) {
    Ci.print_header();
    exit(0);}

  Ci.init_parameters();
  char file_type = 'a';
  if (argc > 2) 
    if (argv[2][0] == 'b')
      file_type = 'b';
  
  Ci.read_input(argv[1],file_type);
 
  Ci.read_parameters(argc,argv,file_type);
  bool ok = Ci.check_init_states();
  assert(ok);
  Ci.assgn_var_type();
  get_runtime (usrtime0, systime0);
  int res = Ci.mic3();
  get_runtime (usrtime, systime);  

  int ret_val;
  printf("\n");
  switch (res) {
  case 0: {
    printf("property HOLDS\n");   
    if (Ci.print_inv_flag) 
      Ci.print_invariant(Ci.print_only_ind_clauses);
    if (Ci.print_clauses_flag)
      Ci.print_fclauses();
    bool ok = Ci.ver_trans_inv();
    if (ok) ret_val = 2;
    else ret_val = 12;
    break;}
  case 1: {
    printf("property FAILED\n");
    Ci.form_cex();  
    if (Ci.print_cex_flag == 1)
      Ci.fprint_cex1();
    else if (Ci.print_cex_flag == 2)
      Ci.fprint_cex2();
    if (Ci.print_clauses_flag) {
      Ci.print_invariant(true);
    }
    bool ok = Ci.ver_cex();
    if (ok)  ret_val = 1;
    else ret_val = 11;
    break;}
  case 2:
    printf("UNDECided\n");
    ret_val = 3;
    if (Ci.print_clauses_flag) 
      Ci.print_fclauses();
    break;
  default:
    assert(false);
  }
  if (Ci.statistics) {
    printf("*********\n");
    if ((Ci.stat_data > 0) && (ret_val < 10)) Ci.print_stat();
    printf("total time is %.2f sec.\n",usrtime-usrtime0);
  }
  exit(ret_val);
} /* end of function main */


/*=================================

  C H E C K _ I N I T _ S T A T E S
  
  =================================*/
bool CompInfo::check_init_states()
{

  for (int i=0; i < Ist.size();i++)
    if (Ist[i].size() != 1) return(false);

  return(true);

} /* end of function check_init_states */


