/*******************************************************************\

Module: CEGAR for BMC

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <trans/ldg.h>

class latch_orderingt
{
public:
  typedef std::vector<unsigned> orderingt;

  // map from node number to ordering number
  orderingt node_ordering;
  
  void compute(ldgt &ldg);

protected:
  void ordering_bfs(unsigned start_node);
};
