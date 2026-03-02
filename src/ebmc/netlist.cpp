/*******************************************************************\

Module: Netlists for EBMC

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "netlist.h"

#include <util/message.h>

#include <solvers/prop/literal_expr.h>
#include <trans-netlist/aig_nondet_elimination.h>
#include <trans-netlist/netlist.h>
#include <trans-netlist/trans_to_netlist.h>
#include <trans-netlist/trans_to_netlist_simple.h>

#include "instrument_past.h"

/// Apply a substitution map to all literal_exprt leaves in an expression.
static void apply_substitution(exprt &expr, const aig_substitution_mapt &map)
{
  if(expr.id() == ID_literal)
  {
    auto &lit_expr = to_literal_expr(expr);
    lit_expr.set_literal(map(lit_expr.get_literal()));
  }
  else
  {
    for(auto &op : expr.operands())
      apply_substitution(op, map);
  }
}

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

  // Eliminate nondet nodes using equivalences, and reorder.
  if(!netlist.equivalences.empty())
  {
    auto old_num_nodes = netlist.number_of_nodes();

    auto [new_aig, map] = aig_nondet_elimination(netlist, netlist.equivalences);

    // Replace the AIG nodes and labeling.
    netlist.nodes = std::move(new_aig.nodes);
    netlist.labeling = std::move(new_aig.labeling);

    // Apply the substitution to all literal references.
    for(auto &l : netlist.constraints)
      l = map(l);

    for(auto &l : netlist.initial)
      l = map(l);

    for(auto &l : netlist.transition)
      l = map(l);

    for(auto &[id, var] : netlist.var_map.map)
      for(auto &bit : var.bits)
      {
        bit.current = map(bit.current);
        if(var.has_next())
          bit.next = map(bit.next);
      }

    netlist.var_map.build_reverse_map();

    for(auto &[id, property_opt] : netlist.properties)
      if(property_opt.has_value())
        apply_substitution(property_opt.value(), map);

    // The equivalences have been applied.
    netlist.equivalences.clear();

    auto new_num_nodes = netlist.number_of_nodes();
    auto eliminated = old_num_nodes - new_num_nodes;
    messaget message{message_handler};
    message.statistics() << "Nondet elimination: eliminated " << eliminated
                         << " of " << old_num_nodes << " nodes ("
                         << (old_num_nodes == 0
                               ? 0
                               : 100 * eliminated / old_num_nodes)
                         << "%)" << messaget::eom;
  }

  // check that the AIG is in dependency order
  netlist.check_ordering();

  return netlist;
}
