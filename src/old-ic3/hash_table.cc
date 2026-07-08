/******************************************************

Module: Functions for creating and updating a 
        hash table

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


/*============================

  S T A R T E D _ U S I N G

  =============================*/
void hsh_tbl::started_using(void)
{

  assert(in_use == false);
  in_use = true;
  
} /* end of function started_using */

/*===========================

  D O N E _ U S I N G

  =============================*/
void hsh_tbl::done_using(void)
{
  in_use = false;

}/* end of function done_using */

/*========================================

  C H A N G E _ M A R K E R

  The function increments or resets the 
  hash table marker
  ========================================*/
void hsh_tbl::change_marker(void)
{
  assert(!in_use);
  if (marker >= MAX_MARKER)
    {marker = 1;
      for (size_t i=0; i < Table.size();i++)
	Table[i] = 0;
      return;
    }
  marker++;

} /* end of function change_marker */
/*========================================

  I N I T

  The function increments or resets the 
  hash table marker
  ========================================*/
void hsh_tbl::hsh_init(int nelems)

{ marker = 1;
  Table.clear();
  Table.assign(nelems,0);
  in_use = false;
} /* end of function init */



/*========================================

  C L E A N

  The function increments or resets the 
  hash table marker
  ========================================*/
void hsh_tbl::clean()

{ marker = 1;
  for (size_t i=0; i < Table.size(); i++)
    Table[i]=0;
} /* end of function clean */



/*========================================

  A D D _ E L E M

  The function allocates memory
  for one more elem.
  ========================================*/
void hsh_tbl::add_elem(void)
{
  Table.push_back(marker);

} /* end of function add_elem */


/*========================================

  S I Z E

  The function allocates memory
  for one more elem.
  ========================================*/
size_t hsh_tbl::size(void)
{
  return(Table.size());

} /* end of function add_elem */


