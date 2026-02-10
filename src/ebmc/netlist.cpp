/*******************************************************************\

Module: Netlists for EBMC

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "netlist.h"

#include <util/message.h>

#include <trans-netlist/netlist.h>
#include <trans-netlist/trans_to_netlist.h>
#include <trans-netlist/trans_to_netlist_simple.h>

#include "instrument_past.h"

netlistt make_netlist(
  transition_systemt &transition_system,
  ebmc_propertiest &properties,
  const cmdlinet &cmdline,
  message_handlert &message_handler)
{
  instrument_past(transition_system, properties);

  netlistt netlist;

  if(cmdline.isset("simple-netlist"))
  {
    convert_trans_to_netlist_simple(
      transition_system.symbol_table,
      transition_system.main_symbol->name,
      transition_system.trans_expr,
      properties.make_property_map(),
      netlist,
      message_handler);
  }
  else
  {
    convert_trans_to_netlist(
      transition_system.symbol_table,
      transition_system.main_symbol->name,
      transition_system.trans_expr,
      properties.make_property_map(),
      netlist,
      message_handler);
  }

  // check that the AIG is in dependency order
  netlist.check_ordering();

  // simplify using equivalences
  auto nodes_before = netlist.number_of_nodes();
  simplify(netlist);
  auto nodes_after = netlist.number_of_nodes();

  messaget message{message_handler};
  message.statistics() << "AIG simplifier removed "
                       << nodes_before - nodes_after << " of "
                       << nodes_before << " nodes ("
                       << (nodes_before == 0
                             ? 0
                             : (nodes_before - nodes_after) * 100 / nodes_before)
                       << "%)" << messaget::eom;

  // again, check that the AIG is in dependency order
  netlist.check_ordering();

  return netlist;
}
