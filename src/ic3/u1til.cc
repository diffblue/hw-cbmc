/******************************************************

Module:  Some auxiliary functions (Part 2)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include "Solver.h"
#include "SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"


/*===========================================

  E X T R _ P R E S  _ S T A T E

  ============================================*/
void CompInfo::extr_pres_state(CUBE &A,SatSolver &Slvr)
{
  
 
  MboolVec &S = Slvr.Mst->model;
  for (int i=0; i < Pres_svars.size(); i++) {
    int var_ind = Pres_svars[i]-1;
    if (S[var_ind] == Mtrue) A.push_back(var_ind+1);
    else A.push_back(-(var_ind+1));
  }

} /* end of function extr_pres_state */


/*===========================================

  E X T R _ N E X T  _ S T A T E

  ============================================*/
void CompInfo::extr_next_state(CUBE &A,SatSolver &Slvr)
{
  MboolVec &S = Slvr.Mst->model;

  for (int i=0; i < Next_svars.size(); i++) {
    int var_ind = Next_svars[i]-1;
    if (S[var_ind] == Mtrue) A.push_back(var_ind+1);
    else A.push_back(-(var_ind+1));
  }
} /* end of function extr_next_state */

/*=================================

  A D D _ F C L A U S E 1

  =================================*/
void CompInfo::add_fclause1(CLAUSE C,int last_ind)
{

  ClauseInfo el;
  int clause_ind = F.size();
  my_assert(C.size() > 0);

  sort(C.begin(),C.end());
  int clause_ind1 = -1;
  int prev_tf_ind = -1;

  if (Clause_table.find(C) != Clause_table.end()) {
    clause_ind1  = Clause_table[C];
    prev_tf_ind = Clause_info[clause_ind1].span;
    update_fclause(clause_ind1,last_ind);
    goto NEXT;
  }
 
  assert((last_ind >= 0) && (last_ind < Time_frames.size()));
  Time_frames[last_ind].num_bnd_cls++;

  
  el.span = last_ind;
  el.active = 1;
  el.skip = 0;
  el.delay = 0;

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
void CompInfo::update_fclause(int clause_ind,int tf_ind)
{

  Time_frames[tf_ind].num_bnd_cls++;
  ClauseInfo &el = Clause_info[clause_ind];
  if (el.span >= tf_ind) {
    p();
    printf("updating clause F[%d]: ",clause_ind);
    printf("F.size() = %d\n",(int) F.size());
    std::cout << F[clause_ind] << std::endl;
    printf("el.span = %d,tf_ind = %d\n",el.span,tf_ind);
    exit(1);
  }

  Time_frames[el.span].num_bnd_cls--;
  el.span = tf_ind;

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


