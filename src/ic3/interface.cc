/******************************************************

Module: Interface between IC3 and SAT-solvers

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>
#include "Solver.h"
#include "SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"


/*=====================
     
  C H E C K _ S A T 1

  ====================*/
bool CompInfo::check_sat1(SatSolver &Slvr) 
{

  Slvr.num_calls++;
  Slvr.tot_num_calls++;
  return(Slvr.Mst->solve());

} /* end of function check_sat1 */

/*=====================
     
  C H E C K _ S A T 2

  ====================*/
bool CompInfo::check_sat2(SatSolver &Slvr,MvecLits &Assmps) 
{

  Slvr.num_calls++;
  Slvr.tot_num_calls++;
  return(Slvr.Mst->solve(Assmps));

} /* end of function check_sat2 */

/*=======================================

  D E L E T E _ S O L V E R

  =======================================*/
void CompInfo::delete_solver(SatSolver &Slvr)
{
  Slvr.prev_oper = DELETE;
  delete Slvr.Mst;

} /* end of function delete_solver */



/*=====================================

  I N I T _ S A T _ S O L V E R

  ===================================*/
void CompInfo::init_sat_solver(SatSolver &Slvr,int nvars,std::string &Id_name) 
{
  bool first_call = (Name_table.find(Id_name) == Name_table.end());

  if (first_call)  {
    Slvr.tot_num_calls = 0;
    Slvr.Name = Id_name;
    Name_table[Id_name] = 1;
  }
  else  // not a first call
    assert(Slvr.prev_oper == DELETE);
   

  Slvr.prev_oper = INIT;
  IctMinisat::Solver *S = new IctMinisat::Solver();
  for (int i = 0; i < nvars; ++i) 
    IctMinisat::Var nv = S->newVar();

  Slvr.init_num_vars = S->nVars();
  Slvr.num_rel_vars = 0;
  Slvr.num_calls = 0;
  Slvr.Mst = S;

} /* end of function init_sat_solver */
