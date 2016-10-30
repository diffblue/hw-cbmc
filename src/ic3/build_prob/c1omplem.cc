/******************************************************

Module: Computing complement of a formula (Part 1)

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

const int MAX_COMPL_GATE = 10;

/*================================

      F I N D _ C O M P L E M

 =================================*/
void CompInfo::find_complem(DNF &R,DNF &F,int num_vars)
{

  assert(num_vars <= MAX_COMPL_GATE);

  int num_mterms = 1 << num_vars;

  DNF Lits0,Lits1;

  for (int i=0; i < num_vars; i++) {
    CUBE Dummy;
    Lits0.push_back(Dummy);
    Lits1.push_back(Dummy);
  }

  find_lit_presence(F,Lits0,Lits1);


  for (int i=0; i < num_mterms; i++) {
    CUBE M;
    conv_to_mterm(M,i,num_vars);
    if (eval_to_1(F,M)) continue;
    if (eval_to_1(R,M)) continue;
    CUBE C;
    expand_mterm(C,F,M,Lits0,Lits1);
    R.push_back(C);
  }
  


} /* end of function find_complem */


/*======================================

     F I N D _ L I T _ P R E S E N C E

 =======================================*/
void CompInfo::find_lit_presence(DNF &F,DNF &Lits0,DNF &Lits1)
{

  for (int i=0; i < F.size(); i++) {
    CUBE &C = F[i];
    for (int j=0; j < C.size(); j++) {
      int lit = C[j];
      if (lit < 0) Lits0[-lit-1].push_back(i);
      else Lits1[lit-1].push_back(i);
    }
  }
  

} /* end of function find_lit_presence */


/*======================================

     C U B E _ C O V E R S _ M T E R M

  ASSUMPTIONS: see those of 'eval_to_1'
  =======================================*/
bool CompInfo::cube_covers_mterm(CUBE &C,CUBE &M)
{

  for (int i=0; i < C.size(); i++) {
    int var_ind = abs(C[i])-1;
    if (M[var_ind] != C[i]) return(false);
  }

  return(true);

} /* end of function cube_covers_mterm */


/*==============================

     E V A L _ T O _ 1 

  ASSUMPTIONS:
   1) 'M' is a minterm
   2) Literals of 'M' are
      ordered in ascending order
      of their index

  =============================*/
bool CompInfo::eval_to_1(DNF &F,CUBE &M)
{

  for (int i=0; i < F.size(); i++) 
    if (cube_covers_mterm(F[i],M)) 
       return(true);

  return(false);

} /* end of function eval_to_1 */


/*====================================

       C O N V _ T O _ M T E R M

  ===================================*/
void CompInfo::conv_to_mterm(CUBE &M,int val,int num_vars)
{

  for (int i=0; i < num_vars; i++) {
    if (val & 1) M.push_back(i+1);
    else M.push_back(-(i+1));
    val >>= 1;
  }

} /* end of function conv_to_mterm */

