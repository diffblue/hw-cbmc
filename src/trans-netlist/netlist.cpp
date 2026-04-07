/*******************************************************************\

Module: Graph representing Netlist

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "netlist.h"

#include <solvers/flattening/boolbv_width.h>

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
