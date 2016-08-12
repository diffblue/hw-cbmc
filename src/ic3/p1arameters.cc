/******************************************************

Module: Reading and ininitialization of parameters

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


/*==============================

  P R I N T _ H E A D E R

  =============================*/
void CompInfo::print_header()
{

  printf("mic3 circ file_type [C|c|d||e|i|n|r|x] [a'num] ['D'num] ['g'num] ['m'val] ['o' name] ['s'num]\n");
  printf("          ['Sl'num] ['Si'num] ['t'num] ['T'num] ['v'num] \n");
  printf("circ     - name of the file containing the initial circuit\n");
  printf("file_type - symbol 'a' (aiger file) or 'b' (blif format file)\n");
  printf("'a'num   - num specifies the activity update mode\n");
  printf("C        - print inductive and local clauses\n");
  printf("c        - print out the counterexample found (if any)\n");
  printf("d        - is used for debugging purposes\n");
  printf("'D'num   - specifies heuristics used to pick a literal\n");
  printf("           0 - random (default), 1 - inactive lit \n");
  printf("           2 - inactive var, 3 - BerkMin like heuristic\n");
  printf("e        - set the selector variables to 1 (used for debugging)\n");
  printf("'g'num   - sets the maximal value of gcount (used for debugging)\n");
  printf("'i'num   - print out the invariant found (if any)\n");
  printf("           if 'num == 1', then only inductive clauses are printed out\n");
  printf("'m'val   - value is a real number specifying the value of the multiplier\n");
  printf("'n'      - does not print any statistics\n");
  printf("o name   - print the result to a file with the root name 'name'\n");
  printf("'r'      - remove subsumed clauses\n");
  printf("'R'      - initial randomization is on\n");
  printf("'s'num   - print statistics, num specifying the level of detail\n");
  printf("'Sl'num  - 'num' specifies literal ordering procedure when lifting a state\n");
  printf("'Si'num  - 'num' specifies literal ordering procedure when building an ind. clause\n");
  printf("'t'num   - stop after num-th time frame is finished\n");
  printf("'T'num   - terminate after 'num' seconds\n");
  printf("'v'num   - print out computation with the level of details  specified by 'num'\n");
  printf("'x'      - print out counterexample as a cnf formula\n");
} /* end of function print_header */

/*=====================================

  I N I T _ P A R A M E T E R S

  =====================================*/
void CompInfo::init_parameters()
{

  print_inv_flag = false;
  print_cex_flag = 0;
  strcpy(out_file,"res");
  verbose = 0;
  gcount_max = -1;
  fin_tf = -1;
  print_only_ind_clauses = 0;
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
  multiplier = 1.05;
  factor = 1.;
  max_act_val = 10000.;
  cut_off_tf = 5;
  max_num_elems = 10;
} /* end of function init_parameters */


/*=====================================

  R E A D _ P A R A M E T E R S

  =====================================*/
void CompInfo::read_parameters(int argc,char *argv[],char file_type)
{

  int start = (file_type == 'a')?2:3; 
  for (int i=start; i < argc; i++) 
    switch(argv[i][0]){
    case 'a':
      act_upd_mode = atoi(argv[i]+1);
      assert(act_upd_mode >=  NO_ACT_UPD);
      assert(act_upd_mode <= MINISAT_ACT_UPD);
      break;      
    case 'C':
      print_clauses_flag = true;
      break;
    case 'c':
      print_cex_flag = 1;
      break;
    case 'd':
      use_short_prop = false;
      break;
    case 'D':
      lit_pick_heur = atoi(argv[i]+1);
      assert(lit_pick_heur >= RAND_LIT);
      assert(lit_pick_heur <= MIXED);
      break;
    case 'e':
      selector = 1;
      break;
    case 'g':
      gcount_max = atoi(argv[i]+1);
      break;
    case 'i':
      print_inv_flag = true;
      if (strlen(argv[i]) > 1)
        print_only_ind_clauses = 1;
      break;  
    case 'm':
      multiplier = atof(argv[i]+1);
      assert(multiplier > 1);
      break;  
    case 'n':
      statistics  = false;
      break;
    case 'o':
      assert(i+1 < argc);
      strcpy(out_file,argv[i+1]);
      i++;
      break;
    case 'r':
      rem_subsumed_flag = true;
      break;
    case 'R':
      srand48(time(0));
      break;
    case 's':
      if (strlen(argv[i]) > 1) {
	stat_data = atoi(argv[i]+1);
	assert(stat_data >= 0);
      }
      break; 
    case 'S':
      if (argv[i][1] == 'l') {
        lift_sort_mode = atoi(argv[i]+2);
	assert(lift_sort_mode >= NO_SORT);
	assert(lift_sort_mode <= PART_SORT);
      }
      else if (argv[i][1] == 'i') {
	ind_cls_sort_mode = atoi(argv[i]+2);
	assert(ind_cls_sort_mode >= NO_SORT);
	assert(ind_cls_sort_mode <= PART_SORT);
      }
      else assert(false);
      break;      
    case 't':
      fin_tf = atoi(argv[i]+1);
      assert(fin_tf > 0);
      break;
    case 'T':
      time_limit = atoi(argv[i]+1);
      assert(time_limit > 0);
      break;   
    case 'v':
      verbose = atoi(argv[i]+1);
      break;
    case 'x':
      print_cex_flag = 2;
      break;
    default:
      printf("unknown parameter %s",argv[i]);
      exit(1);
    }

} /* end of function read_parameters */

