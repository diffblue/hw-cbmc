/*******************************************************************\

Module: Netlists for EBMC

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "netlist.h"

#include <trans-netlist/netlist.h>
#include <trans-netlist/trans_to_netlist.h>

#include "instrument_past.h"

netlistt make_netlist(
  transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  instrument_past(transition_system, properties);

  netlistt netlist;

  convert_trans_to_netlist(
    transition_system.symbol_table,
    transition_system.main_symbol->name,
    transition_system.trans_expr,
    properties.make_property_map(),
    netlist,
    message_handler);

  // check that the AIG is in dependency order
  netlist.check_ordering();

  return netlist;
}
