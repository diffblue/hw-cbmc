/******************************************************

Module: Printing out some statistics of an IC3 run
        (Part 1)

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
#include <util/message.h>

/*==============================

  P R I N T _ S T A T

  =============================*/
void CompInfo::print_stat()
{


  unsigned ms_lev = messaget::M_STATISTICS;
  M->statistics() << "num of time frames = " << max_num_tfs << M->eom;
  if (inv_ind >= 0)   M->statistics() << "inv_ind = " << inv_ind << M->eom;
  my_printf(ms_lev,"#inputs = %m, #outputs = %m, #latches = %m, #gates = %m\n",
	    N->ninputs,N->noutputs,N->nlatches, N->ngates);
  M->statistics() << "total number of generated clauses is " <<  F.size()- 
    Ist.size() + init_ind_cls() << M->eom;

  my_printf(ms_lev,"orig_ind_cls = %m, succ_impr = %m, failed_impr = %m\n",
            orig_ind_cls,succ_impr,failed_impr);
  

  // print the total average size

  M->statistics() << std::fixed;
  M->statistics().precision(1);
  M->statistics() << "Aver. clause size = " << average() << M->eom;

  M->statistics() << "max. num. improv. of an ind. clause is " << max_num_impr << M->eom;
  my_printf(ms_lev,"#add1 = %m, #add2 = %m, #replaced = %m, #restore = %m\n",
            num_add1_cases,num_add2_cases,num_replaced_cases,num_restore_cases);
  print_sat_stat();

  print_flags();

  M->statistics().precision(2);
  M->statistics() << "muliplier = " << multiplier << M->eom;

  print_lifting_stat();
  my_printf(ms_lev,"root_state_cnt = %m, new_state_cnt = %m, old_state_cnt = %m",
            root_state_cnt,new_state_cnt,old_state_cnt);
  my_printf(ms_lev," (triv = %m, rem = %m)\n",triv_old_st_cnt,
            old_state_cnt-triv_old_st_cnt);

 
  my_printf(ms_lev,"#CTGs = %m, #excluded CTGS = %m\n",tot_ctg_cnt,succ_ctg_cnt);
} /* end of function print_stat */


/*============================

  A V E R A G E

  ==========================*/
float CompInfo::average()
{

  float total = 0.;
  for (size_t i=Ist.size(); i < F.size(); i++) {
    total += F[i].size();
  }

  int num_clauses = F.size()-Ist.size();
  if (num_clauses > 0)  return(total * 1. / num_clauses);
  else return(0.);
} /* end of function average */


/*========================================

  P R I N T _ S A T _ S T A T

  =========================================*/
void CompInfo::print_sat_stat(){

  print_one_sat_stat(Gen_sat);
  print_one_sat_stat(Bst_sat);
  print_one_sat_stat(Lbs_sat);
  print_one_sat_stat(Lgs_sat);

  int time_frame_calls;
  print_time_frame_sat_stat(time_frame_calls);

  print_all_calls(time_frame_calls);

} /* end of function print_one_sat_stat */

/*=============================================

  P R I N T _ O N E _ S A T _ S T A T

  =============================================*/
void CompInfo::print_one_sat_stat(SatSolver &S)
{

  if (Name_table.find(S.Name) == Name_table.end()) 
    return;

  M->statistics() << S.Name << ": ";
  M->statistics() << S.tot_num_calls <<  " calls" << M->eom;

} /* end of function print_one_sat_stat */


/*========================================

  P R I N T _ T I M E _ F R A M E _ S T A T

  ========================================*/
void CompInfo::print_time_frame_stat()
{
    
  int time_frame_calls;
  print_time_frame_sat_stat(time_frame_calls);

 
} /* end of function print_time_frame_stat*/


/*===================================================

  P R I N T _ T I M E _ F R A M E _ S A T _ S T A T

  ==================================================*/
void CompInfo::print_time_frame_sat_stat(int &time_frame_calls)
{

  unsigned ms_lev = messaget::M_STATISTICS;
  time_frame_calls = 0;

  for (size_t i=0; i < Time_frames.size(); i++) 
    time_frame_calls += Time_frames[i].Slvr.num_calls;

  my_printf(ms_lev,"Time frame SAT-solvers: %m calls\n",time_frame_calls); 
  my_printf(ms_lev,"Push clause SAT-solving: %m calls\n",num_push_clause_calls);

} /* end of function print_time_frame_sat_stat */

/*=================================================

  P R I N T _ A L L _ C A L L S

  ==================================================*/
void CompInfo::print_all_calls(int time_frame_calls)
{

  unsigned ms_lev = messaget::M_STATISTICS;
  int all_calls = time_frame_calls;
  if (Name_table.find(Gen_sat.Name) != Name_table.end()) 
    all_calls += Gen_sat.tot_num_calls;

  if (Name_table.find(Bst_sat.Name) != Name_table.end()) 
    all_calls += Bst_sat.tot_num_calls;

  if (Name_table.find(Lbs_sat.Name) != Name_table.end()) 
    all_calls += Lbs_sat.tot_num_calls;

  if (Name_table.find(Lgs_sat.Name) != Name_table.end()) 
    all_calls += Lgs_sat.tot_num_calls;



  my_printf(ms_lev,"all solvers: %m calls\n",all_calls);

} /* end of function print_all_calls */



