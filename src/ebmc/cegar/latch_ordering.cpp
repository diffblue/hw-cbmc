/*******************************************************************\

Module: CEGAR for BMC

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "latch_ordering.h"

/*******************************************************************\

Function: latch_orderingt::ordering_bfs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void latch_orderingt::ordering_bfs(unsigned start_node)
{
  /*
    unmark all vertices
    choose some starting vertex x
    mark x
    list L = x
    tree T = x
    while L nonempty
    choose some vertex v from front of list
    visit v
    for each unmarked neighbor w
        mark w
        add it to end of list
        add edge vw to T
  */
}

/*******************************************************************\

Function: latch_orderingt::compute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void latch_orderingt::compute(ldgt &ldg)
{
}
