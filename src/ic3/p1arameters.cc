/******************************************************

Module: Reading and ininitialization of parameters

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
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

/*==============================

     P R I N T _ H E A D E R

  =============================*/
void CompInfo::print_header()
{

  printf("mic3 circ [b|C|c|d||e|i|n|N|r|x] ['a'num] ['D'num] ['g'num]\n");
  printf("          ['h'val] ['m'val] ['o' name] ['p'num] ['s'num] ['Sl'num]"); 
  printf("\n");
  printf("          ['Si'num] ['Sg'num]['t'num] ['T'num] ['v'num] \n\n");
  printf("circ     - name of the file containing the initial circuit\n");
  printf("'a'num   - num specifies the activity update mode\n");
  printf("b        - sets ctg_flag to false\n");
  printf("C        - print inductive and local clauses\n");
  printf("c        - print out the counterexample found (if any)\n");
  printf("d        - is used for debugging purposes\n");
  printf("'D'num   - specifies heuristics used to pick a literal\n");
  printf("           0 - random (default), 1 - inactive lit \n");
  printf("           2 - inactive var, 3 - BerkMin like heuristic\n");
  printf("e        - set the selector variables to 1 (used for debugging)\n");
  printf("'g'num   - sets the maximal value of gcount (used for debugging)\n");
  printf("'i'num   - print out the invariant found (if any)\n");
  printf("           if 'num == 1', only inductive clauses are printed out\n");
  printf("j        - use joins in general. of ind. clauses if 'ctg_flag==0'\n");
  printf("'m'val   - value is a real number used when comp. var. activity\n");
  printf("'n'      - does not print any statistics\n");
  printf("'N'      - set constr_flag to 'false'\n");
  printf("o name   - print the result to a file with the root name 'name'\n");
  printf("'p'num   - num specifies the property index to check \n");
  printf("           (if circuit is specified in the AIGER format)\n");
  printf("'r'      - remove subsumed clauses\n");
  printf("'R'      - initial randomization is on\n");
  printf("'s'num   - print statistics, num specifying the level of detail\n");
  printf("'Sl'num  - 'num' spec. literal ordering when lifting a state\n");
  printf("'Si'num  - 'num' spec. literal ordering when gener. an ind. clause\n");
  printf("'Sg'num  - 'num' spec. gate ordering used to generate CNF formulas\n");
  printf("'t'num   - stop after num-th time frame is finished\n");
  printf("'T'num   - terminate after 'num' seconds\n");
  printf("'v'num   - level of verbosity is  specified by 'num'\n");
  printf("'x'      - print out counterexample as a cnf formula\n");
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
  grl_heur = NO_JOINS;
  max_coi_depth = 10;
  prop_ind = 0;
  constr_flag = true;

  } /* end of function init_parameters */
