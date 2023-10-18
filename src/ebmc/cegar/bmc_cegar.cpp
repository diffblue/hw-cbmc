/*******************************************************************\

Module: CEGAR for BMC

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bmc_cegar.h"

#include <trans-netlist/instantiate_netlist.h>
#include <trans-netlist/unwind_netlist.h>
#include <trans-netlist/ldg.h>
#include <trans-netlist/trans_to_netlist.h>
#include <trans-netlist/compute_ct.h>

#include <cassert>
#include <chrono>

/*******************************************************************\

Function: bmc_cegart::bmc_cegar

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_cegart::bmc_cegar()
{
  if(properties.properties.empty())
  {
    error() << "No properties given" << eom;
    return;
  }

  auto start_time=std::chrono::steady_clock::now();

  try { cegar_loop(); }
  
  catch(int)
  {
  }

  auto stop_time = std::chrono::steady_clock::now();

  statistics()
    << "CEGAR time: "
    << std::chrono::duration<double>(stop_time-start_time).count()
    << eom;
}

/*******************************************************************\

Function: bmc_cegart::unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_cegart::unwind(
  std::size_t bound,
  const netlistt &netlist,
  cnft &solver)
{
  ::unwind(netlist, bmc_map, *this, solver);

  // one of the properties needs to fail
  bvt disjuncts;

  for(auto &property_it : netlist.properties)
  {
    auto &prop_bv = prop_bv_map[property_it.first];
    unwind_property(property_it.second, bmc_map, prop_bv);

    disjuncts.push_back(!solver.land(prop_bv));
  }

  solver.lcnf(disjuncts);
}

/*******************************************************************\

Function: bmc_cegart::compute_ct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::size_t bmc_cegart::compute_ct()
{
  status() << "Computing abstract LDG" << eom;
   
  ldgt ldg;

  ldg.compute(abstract_netlist);

  status() << "Computing abstract CT" << eom;

  auto ct = ::compute_ct(ldg);

  result() << "Abstract CT=" << ct << eom;

  return ct;
}

/*******************************************************************\

Function: bmc_cegart::cegar_loop

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_cegart::cegar_loop()
{
  initial_abstraction=true;

  while(true)
  {
    abstract();

    auto ct = compute_ct();

    if(ct>=MAX_CT)
    {
      error() << "CT too big -- giving up" << eom;
      throw 0;
    }
    
    // this is enough
    auto bound = ct;

    if(verify(bound))
    {
      status() << "VERIFICATION SUCCESSFUL -- PROPERTY HOLDS" << eom;
      return;
    }

    if(simulate(bound))
    {
      status() << "VERIFICATION FAILED -- PROPERTY REFUTED" << eom;
      return;
    }

    refine();
  }
}

/*******************************************************************\

Function: do_bmc_cegar

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int do_bmc_cegar(
  const netlistt &netlist,
  ebmc_propertiest &properties,
  const namespacet &ns,
  message_handlert &message_handler)
{
  bmc_cegart bmc_cegar(netlist, properties, ns, message_handler);

  bmc_cegar.bmc_cegar();
  return 0;
}
