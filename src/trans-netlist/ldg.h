/*******************************************************************\

Module: Latch Dependency Graph

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_LDG_H
#define CPROVER_TRANS_LDG_H

#include <set>

#include <util/graph.h>

#include "netlist.h"

struct ldg_nodet:public graph_nodet<>
{
public:
  bool is_source_latch;
  literalt next_state;
};

class ldgt:public grapht<ldg_nodet>
{
public:
  typedef std::set<unsigned> latchest;
  latchest latches;

  void compute(const netlistt &netlist);

  // compute with respect to a localization reduction
  // the set contains the variable numbers of the
  // latches that are to be considered
  void compute(const netlistt &netlist,
               const latchest &localization);
};

#endif
