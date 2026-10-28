/******************************************************

Module: Printing out a counterexample or an invariant

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>
#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

/*================================

  F P R I N T _ C E X 2

  ===============================*/
void CompInfo::fprint_cex2()
{

  char fname[MAX_NAME];
  strcpy(fname,out_file);
  strcat(fname,".cex.cnf");  
  
  print_dnf(Cex,fname);

} /* end of function fprint_cex2 */


/*================================

  F P R I N T _ C E X 1

  ===============================*/
void CompInfo::fprint_cex1()
{

  char fname[MAX_NAME];
  strcpy(fname,out_file);
  strcat(fname,".cex.txt");  
  FILE *fp = fopen(fname,"w");
  assert(fp != NULL);

  for (size_t i=0; i < Cex.size(); i++) {
    fprintf(fp,"S%zu: ",i);
    CUBE &C = Cex[i];
    for (size_t k=0; k < C.size(); k++) {
      if (k!=0) fprintf(fp," ");
      if (C[k] > 0) fprintf(fp," ");
      fprintf(fp,"%d",C[k]);
    }
    fprintf(fp,"\n");
  }

  fclose(fp);

} /* end of function fprint_cex1 */


/*=================================

  P R I N T _ I N V A R I A N T

  ==================================*/
void CompInfo::print_invariant(bool only_new_clauses)
{

  CNF H;
  CNF Res;
  if (only_new_clauses == false) Res = Prop;
  gen_form1(H,inv_ind+1);
  if (Cex.size() == 0)
    assert(Time_frames[inv_ind].num_bnd_cls == 0);
  add_dnf(Res,H);
  char fname[MAX_NAME];
  strcpy(fname,out_file);
  if (inv_ind < 0) strcat(fname,".clauses.cnf");
  else strcat(fname,".inv.cnf");  
  print_dnf(Res,fname);

} /* end of function print_invariant */

/*=====================================

  P R I N T _ F C L A U S E S

  ======================================*/
void CompInfo::print_fclauses()
{


  char fname[MAX_NAME];
  strcpy(fname,out_file);
  strcat(fname,".clauses.cnf"); 

  CNF Res;

  for (size_t i=Ist.size()-1; i < F.size(); i++) {
    if (Clause_info[i].active == 0) continue;
    Res.push_back(F[i]);
  }

  print_dnf(Res,fname);

} /* end of function print_fclauses */
