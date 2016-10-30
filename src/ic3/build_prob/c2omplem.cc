/******************************************************

Module: Computing complement of a formula (Part 2)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <set>
#include <map>
#include <algorithm>
#include <queue>

#include "Solver.h"
#include "SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "r0ead_blif.hh"
#include "m0ic3.hh"


/*========================

   M A R K _ C U B E S

  =======================*/
void CompInfo::mark_cubes(CCUBE &Marked,CUBE &Cubes)
{

  for (int i=0; i < Cubes.size(); i++) {
    int cube_ind = Cubes[i];
    Marked[cube_ind] = 1;
  }

} /* end of function mark_cubes */


/*================================

       N E W L Y _ M A R K E D

  =================================*/
int CompInfo::newly_marked(CCUBE &Marked,DNF &Lits0,DNF &Lits1,int lit)
{

  int count = 0;
  CUBE *pCubes;

  if (lit < 0) pCubes = &Lits0[-lit-1];
  else pCubes = &Lits1[lit-1];

  for (int i=0; i < pCubes->size(); i++) {
    int cube_ind = (*pCubes)[i];
    if (Marked[cube_ind]) continue;
    count++;
  }

  return(count);

} /* end of function newly_marked */

/*=================================

    P I C K _ B E S T _ L I T

  ==================================*/
int CompInfo::pick_best_lit(CUBE &A,CUBE &M,CCUBE &Marked,DNF &Lits0,
                            DNF &Lits1)
{

  int best_lit = 0;
  int max_value = 0;

  for (int i=0; i < A.size(); i++) {
    int var_ind = abs(A[i])-1;
    if (M[var_ind] == A[i]) continue;
    int num = newly_marked(Marked,Lits0,Lits1,A[i]);
    assert(num > 0);
    if (num > max_value) {
      max_value = num;
      best_lit = -A[i];
    }
  }

  assert(best_lit != 0);
  return(best_lit);
} /* end of function pick_best_lit */


/*======================================

      E X P A N D _ M T E R M

 =======================================*/
void CompInfo::expand_mterm(CUBE &C,DNF &F,CUBE &M,DNF &Lits0,DNF &Lits1)
{

  CCUBE Marked;
  Marked.assign(F.size(),0);
  for (int i=0; i < F.size(); i++) {
    if (Marked[i]) continue;
    int lit = pick_best_lit(F[i],M,Marked,Lits0,Lits1);
    if (lit > 0) mark_cubes(Marked,Lits0[lit-1]);
    else mark_cubes(Marked,Lits1[-lit-1]);
    C.push_back(lit);
  }


} /* end of function expand_mterm */

/*==================================================

    C H E C K _ O V E R L A P P I N G _ C O M P L

  ================================================*/
void CompInfo::check_overlapping_compl(DNF &R,DNF &F) 
{

  for (int i=0; i < R.size(); i++) 
    for (int j=0; j < F.size(); j++) {
      if (overlap_compl(R[i],F[j])) {
	printf("overlapping is found\n");
	printf("R[%d]-> ",i);
	std::cout << R[i] << std::endl;
	printf("F[%d]-> ",j);
	std::cout << F[j] << std::endl;
	exit(1);
      }
    }


} /* end of function check_overlapping_compl */

/*==============================

      O V E R L A P _ C O M P L

  ============================*/
bool CompInfo::overlap_compl(CUBE &A,CUBE &B) 
{

  SCUBE Bs;
  for (int i=0; i < B.size(); i++)
    Bs.insert(B[i]);

  for (int i=0;i < A.size();i++)
    if (Bs.find(-A[i]) != Bs.end())
      return(false);

  return(true);

} /* end of function overlap_compl */

/*===========================================

    C H E C K _ C O M P L E T E N E S S

  ==========================================*/
void CompInfo::check_completeness(DNF &R, DNF &F,int num_vars)
{

   
  int num_mterms = 1 << num_vars;

 
  for (int i=0; i < num_mterms; i++) {
    CUBE M;
    conv_to_mterm(M,i,num_vars);
    if (eval_to_1(F,M)) continue;
    if (eval_to_1(R,M)) continue;
    printf("completeness check failure for minterm:\n");
    std::cout << M << std::endl;
    assert(false);
  }
  

} /* end of function check_completeness */
