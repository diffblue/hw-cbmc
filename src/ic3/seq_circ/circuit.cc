/******************************************************

Module: A few functions for creating/deleting a circuit

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <queue>
#include "dnf_io.hh"
#include "ccircuit.hh"



/*====================================

  C L E A R _ L A B E L S

  ====================================*/
void clear_labels(Circuit *N)
{GCUBE &Gate_list = N->Gate_list;

  for (size_t i=0; i < Gate_list.size();i++)
    Gate_list[i].flags.label = 0;  
  
} /* end of function clear_labels */



/*===================================

  I N I T _ G A T E _ F I E L D S

  ====================================*/
void init_gate_fields(Gate &G)
{
 
  G.seed_gate = -1;
  G.spec_buff_ind = -1;

}/* end of function init_gate_fields */



/*====================================

  C R E A T E _ C I R C U I T 

  The function create a new instance of 
  the type Circuit

  =====================================*/
Circuit *create_circuit(void)
{Circuit *N = new Circuit;

  N->ninputs = 0;
  N->noutputs = 0;
  N->nlatches = 0;
  N->ngates = 0;
  N->max_levels = 0;
  N->nconstants = 0; 
  N->num_spec_buffs = 0;

  return(N);

} /* end of function create_circuit */

/*====================================

  D E L E T E _ C I R C U I T

  =====================================*/
void delete_circuit(Circuit *N)
{
  delete(N);
}/* end of function delete_circuit */

