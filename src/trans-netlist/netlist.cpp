/*******************************************************************\

Module: Graph representing Netlist

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "netlist.h"

#include "aig_simplifier.h"

#include <solvers/flattening/boolbv_width.h>
#include <solvers/prop/literal_expr.h>

#include <ctype.h>
#include <sstream>

/*******************************************************************\

Function: netlistt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void netlistt::print(std::ostream &out) const
{
  var_map.output(out);

  auto reverse_labeling = this->reverse_labeling();

  out << '\n';
  out << "Next state functions:" << '\n';

  // use a sorted var_map to get determistic output
  for(auto it : var_map.sorted())
  {
    const var_mapt::vart &var=it->second;

    for(unsigned i=0; i<var.bits.size(); i++)
    {
      if(var.is_latch())
      {
        out << "  NEXT(" << it->first;
        if(var.bits.size()!=1) out << "[" << i << "]";
        out << ")=";

        print(out, reverse_labeling, var.bits[i].next);

        out << '\n';
      }
    }
  }

  out << '\n';

  out << "Initial state: " << '\n';

  for(auto &c : initial)
  {
    out << "  ";
    print(out, reverse_labeling, c);
    out << '\n';
  }

  out << '\n';

  out << "State invariant constraints: " << '\n';

  for(auto &c : constraints)
  {
    out << "  ";
    print(out, reverse_labeling, c);
    out << '\n';
  }

  out << '\n' << std::flush;

  out << "Transition constraints: " << '\n';

  for(auto &c : transition)
  {
    out << "  ";
    print(out, reverse_labeling, c);
    out << '\n';
  }
  
  out << '\n' << std::flush;
}

static void
apply_substitution(exprt &expr, const substitutiont &substitution)
{
  if(expr.id() == ID_literal)
  {
    auto &literal_expr = to_literal_expr(expr);
    literal_expr.set_literal(
      apply_substitution(literal_expr.get_literal(), substitution));
  }
  else
  {
    for(auto &op : expr.operands())
      apply_substitution(op, substitution);
  }
}

void simplify(netlistt &netlist)
{
  auto [simplified_aig, substitution] =
    aig_simplify(netlist, netlist.equivalences);

  // Replace the AIG nodes and labeling
  netlist.nodes = std::move(simplified_aig.nodes);
  netlist.labeling = std::move(simplified_aig.labeling);

  // Equivalences have been applied
  netlist.equivalences.clear();

  // Apply substitution to constraints
  for(auto &c : netlist.constraints)
    c = apply_substitution(c, substitution);

  // Apply substitution to initial state constraints
  for(auto &c : netlist.initial)
    c = apply_substitution(c, substitution);

  // Apply substitution to transition constraints
  for(auto &c : netlist.transition)
    c = apply_substitution(c, substitution);

  // Apply substitution to var_map
  for(auto &[id, var] : netlist.var_map.map)
    for(auto &bit : var.bits)
    {
      bit.current = apply_substitution(bit.current, substitution);
      if(var.has_next())
        bit.next = apply_substitution(bit.next, substitution);
    }

  // Apply substitution to properties
  for(auto &[id, property_opt] : netlist.properties)
  {
    if(property_opt.has_value())
      apply_substitution(*property_opt, substitution);
  }
}
