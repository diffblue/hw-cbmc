/******************************************************

Module:  Excludes a state from which a bad state is
         reachable (Part 5)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include "Solver.h"
#include "SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"


/*================================

  S U B S U M E S

  This function returns 'true'
  if every literal of 'C' is 
  marked in 'Ht'

  ==============================*/
bool CompInfo::subsumes(CLAUSE &C,hsh_tbl &Ht)
{

  int marker = Ht.marker;
  CUBE &Table = Ht.Table;

  for (int i=0; i < C.size(); i++) {
    int var_ind = abs(C[i])-1;
    if (C[i] < 0) {
      if (Table[var_ind] != marker) 
	return(false);}
    else // C[i] > 0
      if (Table[var_ind+max_num_vars] != marker)
	return(false);
  }

  return(true);
  


} /* end of function subsumes */

/*======================================

  C L A U S E _ O V E R L A P

  Returns 'true' if  C does not contain
  the negation of a literal marked in
  'Ht'

  =====================================*/
bool CompInfo::clause_overlap(CLAUSE &C,hsh_tbl &Ht)
{

  int marker = Ht.marker;
  CUBE &Table = Ht.Table;

  for (int i=0; i < C.size(); i++) {
    int var_ind = abs(C[i])-1;
    if (C[i] < 0) {
      if (Table[var_ind+max_num_vars] == marker) 
	return(false);}
    else // C[i] > 0
      if (Table[var_ind] == marker)
	return(false);
  }

  return(true);

} /* end of function clause_overlap */


/*=====================================

  T R _ R E L _ C L A U S E

  Returns 'true', if 'C' contains a
  variable that is not of 'PRES_ST' type
  =====================================*/
bool CompInfo::tr_rel_clause(CLAUSE &C)
{

  for (int i=0; i < C.size(); i++) {
    int var_ind = abs(C[i])-1;
    if (Var_type[var_ind] != PRES_ST) 
      return(true);
  }

  return(false);

} /* end of function tr_rel_clause */

