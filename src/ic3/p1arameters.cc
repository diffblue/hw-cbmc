/******************************************************

Module: Reading and ininitialization of parameters

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

/*=====================================

      R E A D _ P A R A M E T E R S

 =====================================*/
void ic3_enginet::read_parameters()
{

  if (cmdline.isset("h")) {
    print_header();
    exit(0);
  }

  if (cmdline.isset("property")) 
    Ci.prop_name = cmdline.get_value("property");
  

  if (cmdline.isset("constr")) 
    Ci.constr_flag = true;


  if (cmdline.isset("new-mode"))
    Ci.standard_mode = false;
} /* end of function read_parameters */

/*==============================

     P R I N T _ H E A D E R

  =============================*/
void ic3_enginet::print_header()
{

  std::cout << "ebmc verilog_file --ic3 [--prop nm] [--constr]\n";
  std::cout << "prop nm - check property with name 'nm'\n";
  std::cout << "constr  - use constraints listed in 'verilog_file.cnstr'\n";
} /* end of function print_header */

/*=====================================

     I N I T _ P A R A M E T E R S

 =====================================*/
void CompInfo::init_parameters()
{

  print_inv_flag = false;
  print_only_ind_clauses = 0;
  print_cex_flag = 0;
  strcpy(out_file,"res");
  verbose = 0;
  gcount_max = -1;
  fin_tf = -1;
  time_limit = -1;
  use_short_prop = true;
  stat_data = 1;
  selector = 0;  
  print_clauses_flag = false;
  statistics = true;
  rem_subsumed_flag = true;
  lit_pick_heur = INACT_VAR;
  act_upd_mode = MINISAT_ACT_UPD;
  sorted_objects = VARS;
  lift_sort_mode = FULL_SORT;
  ind_cls_sort_mode = FULL_SORT;
  gate_sort_mode = INPS_FIRST;
  multiplier = 1.05;
  factor = 1.;
  max_act_val = 10000.;
  max_num_elems = 10;
  ctg_flag = true;
  max_ctg_cnt = 3;
  max_rec_depth = 1;
  max_coi_depth = 10;
  constr_flag = false;
  standard_mode = true;
  
  } /* end of function init_parameters */

