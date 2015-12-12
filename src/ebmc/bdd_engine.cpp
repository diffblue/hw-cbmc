/*******************************************************************\

Module: BDD Engine

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#include <iostream>

#include "miniBDD/miniBDD.h"

#include "ebmc_base.h"
#include "bdd_engine.h"

/*******************************************************************\

   Class: bdd_enginet

 Purpose:

\*******************************************************************/

class bdd_enginet:public ebmc_baset
{
public:
  bdd_enginet(const cmdlinet &cmdline):ebmc_baset(cmdline)
  {
  }

  int operator()();

protected:
  miniBDD::mgr mgr;

  typedef miniBDD::BDD BDD;
  std::vector<BDD> transition, initial, properties;
  
  void build_trans(const netlistt &);
  
  static inline BDD aig2bdd(
    literalt l,
    const std::vector<BDD> &BDDs)
  {
    assert(l.var_no()<BDDs.size());
    BDD result=BDDs[l.var_no()];
    if(l.sign()) result=!result;
    return result;
  }
};

/*******************************************************************\

Function: do_bdd

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int do_bdd(const cmdlinet &cmdline)
{
  return bdd_enginet(cmdline)();
}

/*******************************************************************\

Function: bdd_enginet::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int bdd_enginet::operator()()
{
  int result=get_model();
  if(result!=-1) return result;

  {  
    status() << "Building netlist" << eom;

    netlistt netlist;

    if(make_netlist(netlist))
    {
      error() << "Failed to build netlist" << eom;
      return 2;
    }

    status() << "Building BDD for netlist" << eom;
    
    build_trans(netlist);
    
    // netlist no longer needed
  }
  
  statistics() << "BDD nodes: "
               << mgr.number_of_nodes() << eom;
  
  if(cmdline.isset("show-bdds"))
  {
    mgr.DumpTable(std::cout);
    return 0;
  }

  if(properties.empty())
  {
    error() << "no properties" << eom;
    return 1;
  }

  return 0;
}

/*******************************************************************\

Function: bdd_enginet::build_trans

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bdd_enginet::build_trans(const netlistt &netlist)
{
  std::vector<BDD> BDDs;
  BDDs.resize(netlist.nodes.size());

  for(unsigned i=0; i<netlist.nodes.size(); i++)
  {
    const netlistt::nodet &n=netlist.nodes[i];
  
    // A node is either an 'and' or a variable
    if(n.is_and())
    {
      BDD a=aig2bdd(n.a, BDDs);
      BDD b=aig2bdd(n.b, BDDs);
    
      BDDs[i]=a & b;
    }
    else // variable
    {
      std::string description=
        netlist.var_map.reverse(i).as_string();
         
      BDDs[i]=mgr.Var(description);
    }
  }
  
  // initial state conditions
  for(literalt l : netlist.initial)
    initial.push_back(aig2bdd(l, BDDs));
    
  // transition conditions
  for(literalt l : netlist.transition)
    transition.push_back(aig2bdd(l, BDDs));
    
  // properties
  for(literalt l : netlist.properties)
    properties.push_back(aig2bdd(l, BDDs));
}
