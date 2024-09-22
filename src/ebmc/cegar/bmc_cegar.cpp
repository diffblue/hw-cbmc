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
  make_netlist();

  if(properties.properties.empty())
  {
    message.error() << "No properties given" << messaget::eom;
    return;
  }

  auto start_time=std::chrono::steady_clock::now();

  try { cegar_loop(); }
  
  catch(int)
  {
  }

  auto stop_time = std::chrono::steady_clock::now();

  message.statistics()
    << "CEGAR time: "
    << std::chrono::duration<double>(stop_time - start_time).count()
    << messaget::eom;
}

/*******************************************************************\

Function: bmc_cegart::unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_cegart::unwind(std::size_t bound, const netlistt &netlist, propt &prop)
{
  // allocate timeframes
  const auto bmc_map = bmc_mapt{netlist, bound + 1, prop};

#if 0
  for(std::size_t timeframe=0; timeframe<=bound; timeframe++)
    bmc_map.timeframe_map[timeframe].resize(aig_map.no_vars);

  // do initial state
  for(std::size_t v=0; v<aig_map.no_vars; v++)
    bmc_map.timeframe_map[0][v]=prop.new_variable();

  // do transitions
  for(std::size_t timeframe=0; timeframe<bound; timeframe++)
  {
    message.status() << "Round " << timeframe << eom;
    
    aig.clear_convert_cache();
    
    // set current state bits
    for(std::size_t v=0; v<aig_map.no_vars; v++)
    {
      //std::cout << "SETTING "
      //          << aig_map.timeframe_map[0][v] << std::endl;

      aig.set_l(prop,
                      aig_map.timeframe_map[0][v],
                      bmc_map.timeframe_map[timeframe][v]);
    }

    // convert next state bits
    for(std::size_t v=0; v<aig_map.no_vars; v++)
    {
      literalt a=aig_map.timeframe_map[1][v];
    
      // std::cout << "CONVERTING " << a << std::endl;

      literalt l;

      if(latches.find(v)!=latches.end())
      {
        assert(aig.can_convert(a));

        l=aig.convert_prop(prop, a);
      }
      else
        l=prop.new_variable();
      
      bmc_map.timeframe_map[timeframe+1][v]=l;
    }
  }

  instantiate(prop, bmc_map, initial_state_predicate, 0, 1,
              false, ns);
  
  // do the property
  property(properties, prop_bv, get_message_handler(), prop,
           bmc_map, ns);
#endif
}

/*******************************************************************\

Function: bmc_cegart::compute_ct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::size_t bmc_cegart::compute_ct()
{
  message.status() << "Computing CT" << messaget::eom;

  message.status() << "Computing abstract LDG" << messaget::eom;

  ldgt ldg;

  ldg.compute(abstract_netlist);

  message.status() << "Computing CT" << messaget::eom;

  std::size_t ct = ::compute_ct(ldg);

  message.result() << "CT=" << ct << messaget::eom;

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

    std::size_t ct = compute_ct();

    if(ct>=MAX_CT)
    {
      message.error() << "CT too big -- giving up" << messaget::eom;
      throw 0;
    }
    
    // this is enough
    std::size_t bound = ct;

    if(verify(bound))
    {
      message.status() << "VERIFICATION SUCCESSFUL -- PROPERTY HOLDS"
                       << messaget::eom;
      return;
    }

    if(simulate(bound))
    {
      message.status() << "VERIFICATION FAILED -- PROPERTY REFUTED"
                       << messaget::eom;
      return;
    }

    refine();
  }
}

/*******************************************************************\

Function: bmc_cegart::make_netlist

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_cegart::make_netlist()
{
  // make net-list
  message.status() << "Making Netlist" << messaget::eom;

  try
  {
    auto property_map = properties.make_property_map();

    convert_trans_to_netlist(
      symbol_table,
      main_module,
      property_map,
      concrete_netlist,
      message.get_message_handler());
  }
  
  catch(const std::string &error_msg)
  {
    message.error() << error_msg << messaget::eom;
    return;
  }

  message.statistics() << "Latches: " << concrete_netlist.var_map.latches.size()
                       << ", nodes: " << concrete_netlist.number_of_nodes()
                       << messaget::eom;
}
