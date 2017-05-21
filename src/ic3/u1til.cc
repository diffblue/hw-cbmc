/******************************************************

Module:  Some auxiliary functions (Part 2)

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



/*=================================

       A D D _ F C L A U S E 1

  =================================*/
void CompInfo::add_fclause1(CLAUSE &C,int last_ind,char st_descr)
{

  ClauseInfo el;
  int clause_ind = F.size();
  assert(C.size() > 0);

  sort(C.begin(),C.end());
 
  int clause_ind1 = -1;
  int prev_tf_ind = -1;

  if (Clause_table.find(C) != Clause_table.end()) {
    clause_ind1  = Clause_table[C];
    prev_tf_ind = Clause_info[clause_ind1].span;
    if (update_fclause(clause_ind1,last_ind) == false) 
      return;
    goto NEXT;
  }

 
  assert((last_ind >= 0) && ((size_t) last_ind < Time_frames.size()));
  Time_frames[last_ind].num_bnd_cls++;

  
  el.span = last_ind;
  el.active = 1;
  el.skip = 0;

  Clause_info.push_back(el);
  
  
  Clause_table[C] = F.size();



  F.push_back(C);
  

 
  upd_act_lit_cnts(C,last_ind);
  


 NEXT:
  int start_ind = 1;
  if (prev_tf_ind >= 0) {
    start_ind = prev_tf_ind+1;
    clause_ind = clause_ind1;
  }
  for (int i=start_ind; i <= last_ind; i++) {
    accept_new_clause(Time_frames[i].Slvr,C);
    Time_frames[i].Clauses.push_back(clause_ind);
  }

} /* end of function add_fclause1 */


/*=========================================

       U P D A T E _ F C L A U S E

  ========================================*/
bool CompInfo::update_fclause(int clause_ind,int tf_ind)
{

  Time_frames[tf_ind].num_bnd_cls++;

  ClauseInfo &el = Clause_info[clause_ind];
  assert(tf_ind>0);
  if (el.span >= (size_t) tf_ind) 
    return(false);
 

  Time_frames[el.span].num_bnd_cls--;
  el.span = tf_ind;

  return(true);

} /* end of function update_fclause */




/*==========================

  R E A D _ N U M B E R S

  =========================*/
void read_numbers(char *buf,int &num1,int &num2)
{
  int pnt=0;

  char loc_buf[MAX_NAME+1];

  // read in the first number
  int loc_pnt = 0;
  while (true)
    {char c = buf[pnt++];
     if (c == ' ') break;
     loc_buf[loc_pnt++] = c;
    }

  loc_buf[loc_pnt] = 0;
  num1 = atoi(loc_buf);

  // skip spaces
  while (true)
    {char c = buf[pnt];
     if (c == ' ') pnt++;
     else break;
    }

    // read in the second number
  loc_pnt = 0;
  while (true)
    {char c = buf[pnt++];
     if (c == ' ')  break;
     if (c == '\n') break;
     loc_buf[loc_pnt++] = c;
    }
loc_buf[loc_pnt] = 0;
 num2 = atoi(loc_buf);
} /* end of function read_numbers */

/*========================

    M Y _ A S S E R T

  ======================*/
void my_assert(bool cond)
{
  if (!cond) {
    p();
    exit(100);
  }
} /* end of function my_assert */


/*=================================

   C H E C K _ I N I T _ S T A T E S
  
  =================================*/
bool CompInfo::check_init_states()
{

  for (size_t i=0; i < Ist.size();i++)
    if (Ist[i].size() != 1) return(false);

  return(true);

} /* end of function check_init_states */

/*===============================================
   
  I N I T _ S T _ S A T I S F Y _ C O N S T R S

   returns 'true' if the initial states satisfy
   the constraints

  ==============================================*/
bool CompInfo::init_st_satisfy_constrs() 
{
  for (size_t i=0; i < Ist.size(); i++) {
    CLAUSE &C = Ist[i];
    assert(C.size() == 1);
    int lit = C[0];
    if (lit < 0) {
      if (Var_info[-lit-1].value == 1)
	return(false);
    }
    else // lit > 0
      if (Var_info[lit-1].value == 0)
	return(false);
  }

  return(true);

} /* end of function init_st_satisfy_constrs */
