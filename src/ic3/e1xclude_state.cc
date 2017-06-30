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
    std::cout << "======\n";
    std::cout << "   exclude_state_cube\n";
    std::cout << St0_cube << std::endl;
  }


  assert(Pr_queue.empty());
  Obl_table.clear();

  assert(tf_lind > 0);
  int curr_tf = tf_lind-1;

  
  add_new_elem(St0_cube,Inps0,curr_tf,1,-1,ROOT_STATE);
  min_tf = curr_tf; 
  while (Pr_queue.size() > 0) {   
    if (verbose > 1)  {
      std::cout << "Pr_queue.size() = " << Pr_queue.size() << std::endl;
    }

    int curr_tf = Pr_queue.top().tf_ind;
    int tbl_ind = Pr_queue.top().tbl_ind;
    
    if (verbose > 1)
      std::cout << "curr_tf = " << curr_tf << ", tbl_ind = " << curr_tf
		<< ", min_tf = " << min_tf << std::endl;

    CUBE St_cube  =  Obl_table[tbl_ind].St_cb;
    char st_descr = Obl_table[tbl_ind].st_descr;


    if (curr_tf == 0) 
      if (cont_init_states(St_cube)) return;

    int dist = Obl_table[tbl_ind].dist;
    int st_ind = tf_lind + 1 - dist;
    
    int succ_ind = Obl_table[tbl_ind].succ_ind;
  
    bool ok = oblig_is_active(curr_tf+1,St_cube);

    if (!ok) {
      if (st_descr == OLD_STATE) triv_old_st_cnt++;
      Pr_queue.pop();     
      if (succ_ind < 0) form_res_cnf(G,curr_tf+1,St_cube);
      continue;}

   
    if (curr_tf < min_tf) min_tf = curr_tf;

    
   
    CLAUSE C;
    bool found = gen_ind_clause(C,St_cube,curr_tf,st_descr);
    

    if (found) { // inductive clause is found      
      Pr_queue.pop();
      if (verbose > 1) 	{	 
	std::cout << "Inductive clause F[" << F.size() << "] is found ";
	std::cout  << C << std::endl;
      }

      if (succ_ind == -1) 
	G.push_back(C);
            
  // the set of obligations is not empty yet
      
      int tf_ind1 = curr_tf+1;

      if (standard_mode)
	tf_ind1 = push_on_the_fly(curr_tf+1,C,st_descr);

      add_fclause1(C,tf_ind1,st_descr);

      if (standard_mode) {
	if (tf_ind1 <= tf_lind) {
	  CUBE Inps = Obl_table[tbl_ind].Inp_assgn;
	  add_new_elem(St_cube,Inps,tf_ind1,dist,succ_ind,OLD_STATE);
	}
      }
      else
	if (tf_ind1 < tf_lind) {
	  CUBE Inps = Obl_table[tbl_ind].Inp_assgn;
	  add_new_elem(St_cube,Inps,tf_ind1+1,dist,succ_ind,OLD_STATE);
	}
     
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
      std::cout << "st_ind = " << st_ind << ", curr_tf = " << curr_tf 
		<< std::endl;     
      throw(ERROR1);
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
    std::cout << std::string(6,' ');
    std:: cout << "find_prev_state_cube\n";
    std:: cout << "curr_tf = " << curr_tf << std::endl;
  }
 
  CUBE Nst_cube;
  conv_to_next_state(Nst_cube,St_cube);
 
  MvecLits Assmps;
  add_assumps1(Assmps,Nst_cube);
 
  
  bool sat_form = check_sat2(Slvr,Assmps);
 
  
  if (sat_form) {
    CUBE St0;
    extr_cut_assgns1(St0,Pres_svars,Slvr);
    extr_cut_assgns1(Prev_inps,Inp_vars,Slvr);
    lift_good_state(Prv_st_cube,St0,Prev_inps,Nst_cube);
    if (verbose > 2) {
      std::cout << std::string(6,' ');
      std:: cout << "Prv. state cube is found: ";
      std::cout << Prv_st_cube << std::endl;
    }
    return(true);
  }

  // formula is unsatisfiable
 
  
  gen_assump_clause(C,Slvr,Assmps);
  return(false);

} /* end of function find_prev_state_cube */
