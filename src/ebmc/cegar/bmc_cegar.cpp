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

  if(properties.empty())
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
  unsigned bound,
  const netlistt &netlist,
  propt &prop)
{
  // allocate timeframes
  const auto bmc_map = bmc_mapt{netlist, bound + 1, prop};

#if 0
  for(unsigned timeframe=0; timeframe<=bound; timeframe++)
    bmc_map.timeframe_map[timeframe].resize(aig_map.no_vars);

  // do initial state
  for(unsigned v=0; v<aig_map.no_vars; v++)
    bmc_map.timeframe_map[0][v]=prop.new_variable();

  // do transitions
  for(unsigned timeframe=0; timeframe<bound; timeframe++)
  {
    status() << "Round " << timeframe << eom;
    
    aig.clear_convert_cache();
    
    // set current state bits
    for(unsigned v=0; v<aig_map.no_vars; v++)
    {
      //std::cout << "SETTING "
      //          << aig_map.timeframe_map[0][v] << std::endl;

      aig.set_l(prop,
                      aig_map.timeframe_map[0][v],
                      bmc_map.timeframe_map[timeframe][v]);
    }

    // convert next state bits
    for(unsigned v=0; v<aig_map.no_vars; v++)
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

unsigned bmc_cegart::compute_ct()
{
  status() << "Computing CT" << eom;

  status() << "Computing abstract LDG" << eom;
   
  ldgt ldg;
 
  ldg.compute(abstract_netlist);
    
  status() << "Computing CT" << eom;

  unsigned ct=::compute_ct(ldg);

  result() << "CT=" << ct << eom;

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
    
    unsigned ct=compute_ct();

    if(ct>=MAX_CT)
    {
      error() << "CT too big -- giving up" << eom;
      throw 0;
    }
    
    // this is enough
    unsigned bound=ct;
    
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

Function: bmc_cegart::make_netlist

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_cegart::make_netlist()
{
  // make net-list
  status() << "Making Netlist" << eom;

  try
  {
    const symbolt &module_symbol = ns.lookup(main_module);
    const transt &trans = to_trans_expr(module_symbol.value);

    std::map<irep_idt, exprt> property_map;

    convert_trans_to_netlist(
      symbol_table,
      main_module,
      trans,
      property_map,
      concrete_netlist,
      get_message_handler());
  }
  
  catch(const std::string &error_msg)
  {
    error() << error_msg << eom;
    return;
  }

  statistics() 
    << "Latches: " << concrete_netlist.var_map.latches.size()
    << ", nodes: " << concrete_netlist.number_of_nodes() << eom;
}
