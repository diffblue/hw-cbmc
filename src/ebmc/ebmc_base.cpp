/*******************************************************************\

Module: Base for Verification Modules

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ebmc_base.h"

#include <util/cmdline.h>
#include <util/config.h>

#include <trans-netlist/compute_ct.h>
#include <trans-netlist/ldg.h>

#include "ebmc_error.h"
#include "ebmc_version.h"
#include "netlist.h"

#include <iostream>

/*******************************************************************\

Function: ebmc_baset::ebmc_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ebmc_baset::ebmc_baset(
  const cmdlinet &_cmdline,
  ui_message_handlert &_ui_message_handler)
  : message(_ui_message_handler), cmdline(_cmdline)
{
}

/*******************************************************************\

Function: ebmc_baset::get_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::get_properties()
{
  properties = ebmc_propertiest::from_command_line(
    cmdline, transition_system, message.get_message_handler());

  return -1; // done
}

/*******************************************************************\

Function: ebmc_baset::show_ldg

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_baset::show_ldg(std::ostream &out)
{
  netlistt netlist;

  if(make_netlist(netlist))
    return;
  
  if(!netlist.transition.empty())
    out << "WARNING: transition constraint found!" << '\n'
        << '\n';
  
  ldgt ldg;
 
  ldg.compute(netlist);
    
  out << "Latch dependencies:" << '\n';

  for(auto var_it : netlist.var_map.sorted())
  {
    auto &var = var_it->second;

    for(std::size_t i=0; i<var.bits.size(); i++)
    {
      if(var.is_latch())
      {
        literalt::var_not v=var.bits[i].current.var_no();

        out << "  " << var_it->first << "[" << i << "] = " << v << ":";

        const ldg_nodet &node=ldg[v];

        for(ldg_nodet::edgest::const_iterator
            i_it=node.in.begin();
            i_it!=node.in.end();
            i_it++)
          out << " " << i_it->first;

        out << '\n';
      }
    }
  }
}

/*******************************************************************\

Function: ebmc_baset::make_netlist

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ebmc_baset::make_netlist(netlistt &netlist)
{
  // make net-list
  message.status() << "Generating Netlist" << messaget::eom;

  try
  {
    netlist = ::make_netlist(
      transition_system, properties, message.get_message_handler());
  }
  
  catch(const std::string &error_str)
  {
    message.error() << error_str << messaget::eom;
    return true;
  }

  message.statistics() << "Latches: " << netlist.var_map.latches.size()
                       << ", nodes: " << netlist.number_of_nodes()
                       << messaget::eom;

  return false;
}

/*******************************************************************\

Function: ebmc_baset::do_compute_ct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::do_compute_ct()
{
  // make net-list
  message.status() << "Making Netlist" << messaget::eom;

  netlistt netlist;
  if(make_netlist(netlist)) return 1;

  message.status() << "Latches: " << netlist.var_map.latches.size()
                   << ", nodes: " << netlist.number_of_nodes() << messaget::eom;

  message.status() << "Making LDG" << messaget::eom;

  ldgt ldg;
  ldg.compute(netlist);

  std::cout << "CT = " << compute_ct(ldg) << '\n';
  
  return 0;
}
