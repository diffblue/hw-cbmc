/******************************************************

Module: Printing out a counterexample or an invariant

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>
#include <fstream>
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

  std::string fname = out_file;
  fname += ".cex.cnf";
  
  bool success = print_dnf(Cex,fname);
  if (!success) {
    M->error() << "cannot open file " << fname << M->eom;
    throw(ERROR2);
  }

} /* end of function fprint_cex2 */


/*================================

  F P R I N T _ C E X 1

  ===============================*/
void CompInfo::fprint_cex1()
{

  std::string fname = out_file;
  fname += ".cex.txt";

  std::ofstream Out_str(fname.c_str(),std::ios::out);
  if (!Out_str) {
    std::cout << "cannot open file " << fname << "\n";
    throw(ERROR2);}

  for (size_t i=0; i < Cex.size(); i++) {
    Out_str << "S" << i << ": ";
    CUBE &C = Cex[i];
    for (size_t k=0; k < C.size(); k++) {
      if (k!=0) Out_str << " ";
      if (C[k] > 0) Out_str << " ";
      Out_str << C[k];
    }
    Out_str << "\n";
  }

  Out_str.close();

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
  std::string fname = out_file;
  
  if (inv_ind < 0) fname += ".clauses.cnf";
  else fname +=".inv.cnf";
  bool success = print_dnf(Res,fname);
  if (!success) {
    M->error() << "cannot open file " << fname << M->eom;
    throw(ERROR2);
  }

} /* end of function print_invariant */

/*=====================================

  P R I N T _ F C L A U S E S

  ======================================*/
void CompInfo::print_fclauses()
{


  std::string fname = out_file;
  fname += ".clauses.cnf";

  CNF Res;

  for (size_t i=Ist.size()-1; i < F.size(); i++) {
    if (Clause_info[i].active == 0) continue;
    Res.push_back(F[i]);
  }

  bool success = print_dnf(Res,fname);
  if (!success) {
    M->error() << "cannot open file " << fname << M->eom;
    throw(ERROR2);
  }

} /* end of function print_fclauses */
