/******************************************************

Module:  Excludes a state from which a bad state is
         reachable (Part 1)

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
/*======================================

  E X C L U D E _ S T A T E _ C U B E

  ======================================*/
void CompInfo::exclude_state_cube(CNF &G,int &min_tf,CUBE &St0_cube,CUBE &Inps0)
{
  if (verbose > 1)  {
    printf("======\n");
    printf("   exclude_state_cube\n");
    std::cout << St0_cube << std::endl;
  }


  int count = 0;
  assert(Pr_queue.empty());
  Obl_table.clear();

  assert(tf_lind > 0);
  int curr_tf = tf_lind-1;

  
  add_new_elem(St0_cube,Inps0,curr_tf,1,-1,ROOT_STATE);
  min_tf = curr_tf; 
  while (Pr_queue.size() > 0) {   
    if (verbose > 1)  {
      printf("Pr_queue.size() = %d\n",(int) Pr_queue.size());
    }

    int obl_tf = Pr_queue.top().tf_ind;
    int tbl_ind = Pr_queue.top().tbl_ind;
    
    if (verbose > 1)
      printf("obl_tf = %d, tbl_ind = %d, min_tf = %d\n",obl_tf,tbl_ind, min_tf);

    CUBE St_cube  =  Obl_table[tbl_ind].St_cb;
    char st_descr = Obl_table[tbl_ind].st_descr;


    if (obl_tf == 0) 
      if (cont_init_states(St_cube)) return;

    int dist = Obl_table[tbl_ind].dist;
    int st_ind = tf_lind + 1 - dist;

    curr_tf = obl_tf;
    int succ_ind = Obl_table[tbl_ind].succ_ind;

    bool ok = oblig_is_active(obl_tf+1,St_cube);

    if (!ok) {
      if (st_descr == OLD_STATE) triv_old_st_cnt++;
      Pr_queue.pop();     
      if (succ_ind < 0) form_res_cnf(G,obl_tf+1,St_cube);
      continue;}

   
    if (obl_tf < min_tf) min_tf = obl_tf;

    
   
    CLAUSE C;
    bool found = gen_ind_clause(C,St_cube,curr_tf,st_descr);
    

    if (found) { // inductive clause is found      
      Pr_queue.pop();
      if (verbose > 1) 	{	 
	printf("Inductive clause F[%d] is found ",(int) F.size());
	std::cout  << C << std::endl;
      }

 
      if (obl_tf + 2 < tf_lind + 1) {
	CUBE Inps = Obl_table[tbl_ind].Inp_assgn;
	add_new_elem(St_cube,Inps,obl_tf+2,dist,succ_ind,OLD_STATE);
      }
     
      
      if (succ_ind == -1) {
	G.push_back(C);
	add_fclause1(C,curr_tf+1,st_descr);	 
	continue;
      } 
	 
      // the set of obligations is not empty yet      
      add_fclause1(C,curr_tf+1,st_descr);
      continue;
    }
    
    // no inductive clause is found  
    C.clear();
    CUBE Erl_st_cube;
    CUBE Erl_inps;
 
    Time_frames[curr_tf].tot_num_ctis++;
    Time_frames[curr_tf].num_rcnt_ctis++;
   
    bool state_found = find_prev_state_cube(C,curr_tf,Erl_st_cube,Erl_inps,
                       St_cube);

    if (state_found == 0) {
      p();
      printf("st_ind = %d, curr_tf = %d\n",st_ind,curr_tf);
      exit(100);
    }
    
    add_new_elem(Erl_st_cube,Erl_inps,curr_tf-1,dist+1,tbl_ind,NEW_STATE);
    if (curr_tf == 0) return;
      
  }

 
} /* end of function exclude_state_cube */


/*=============================

  G E N _ I N D _ C L A U S E

  =============================*/
bool CompInfo::gen_ind_clause(CLAUSE &Res,CUBE &St,int tf_ind,char st_descr)
{
  
  CLAUSE C0,C1;
  form_lngst_clause(C0,St);


  SatSolver &Slvr = Time_frames[tf_ind].Slvr;
  bool found = find_ind_subclause_cti(C1,Slvr,C0,st_descr);
   
  if (!found) return(false); 

  orig_ind_cls++;
 
  shorten_clause(Res,tf_ind,C1,st_descr,0);

  return(true);

} /* end of function gen_ind_clause */


/*=====================================

  A D D _ N E W _ C L A U S E S

  ====================================*/
void CompInfo::add_new_clauses(SatSolver &Slvr,CUBE &Clauses)
{

  for (size_t i=0; i < Clauses.size(); i++)  {
    int clause_ind = Clauses[i];
    assert(clause_ind >= 0);
    accept_new_clause(Slvr,F[clause_ind]);
  }

} /* end of function add_new_clauses */


/*============================================

  F I N D _ P R E V _ S T A T E _ C U B E

  Returns 'true' if a previous state
  is found. Otherwise, returns 'false'

  ==========================================*/
bool CompInfo::find_prev_state_cube(CLAUSE &C,int curr_tf,CUBE &Prv_st_cube,
                                    CUBE &Prev_inps,CUBE &St_cube) 

{

  SatSolver &Slvr = Time_frames[curr_tf].Slvr;
 

  if (verbose > 1) {
    printf("%*c",6,' ');
    printf("find_prev_state_cube\n");
    printf("curr_tf = %d\n",curr_tf);
  }
 
  CUBE Nst_cube;
  conv_to_next_state(Nst_cube,St_cube);
 
  MvecLits Assmps;
  add_assumps1(Assmps,Nst_cube);
 
  
  bool sat_form = check_sat2(Slvr,Assmps);
 
  
  bool ok = true;
  if (sat_form) {
    CUBE St0;
    extr_cut_assgns1(St0,Pres_svars,Slvr);
    extr_cut_assgns1(Prev_inps,Inp_vars,Slvr);
    lift_good_state(Prv_st_cube,St0,Prev_inps,Nst_cube);
    if (verbose > 2) {
      printf("%*c",6,' ');
      printf("Prv. state cube is found: ");
      std::cout << Prv_st_cube << std::endl;
    }
    return(true);
  }

  // formula is unsatisfiable
 
  
  gen_assump_clause(C,Slvr,Assmps);
  return(false);

} /* end of function find_prev_state_cube */
