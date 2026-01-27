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

/*******************************************************************\

Function: dot_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::string dot_id(const std::string &id)
{
  std::string in=id;

  std::string::size_type pos;

  pos=in.rfind("::");

  if(pos!=std::string::npos)
    in=std::string(in, pos+2, std::string::npos);

  pos=in.rfind(".");

  if(pos!=std::string::npos)
    in=std::string(in, pos+1, std::string::npos);

  std::string result;

  result.reserve(in.size());

  for(unsigned i=0; i<in.size(); i++)
  {
    char ch=in[i];
    if(isalnum(ch) || ch=='(' || ch==')' || ch==' ' || ch=='.')
      result+=ch;
    else
      result+='_';
  }

  return result;
}

/*******************************************************************\

Function: netlistt::label

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string netlistt::label(unsigned v) const
{
  PRECONDITION(v < number_of_nodes());
  PRECONDITION(nodes[v].is_var());
  const bv_varidt &varid=var_map.reverse(v);
  const var_mapt::mapt::const_iterator v_it=var_map.map.find(varid.id);
  if(v_it!=var_map.map.end() && v_it->second.bits.size()!=1)
    return id2string(varid.id)+'['+std::to_string(varid.bit_nr)+']';
  else
    return id2string(varid.id);
}

/*******************************************************************\

Function: netlistt::dot_label

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string netlistt::dot_label(unsigned v) const
{
  return dot_id(label(v));
}

/*******************************************************************\

Function: netlistt::output_dot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void netlistt::output_dot(std::ostream &out) const
{
  aigt::output_dot(out);

  // Add the sinks.
  // Use a sorted var_map to get deterministic results.
  for(auto it : var_map.sorted())
  {
    const var_mapt::vart &var=it->second;

    if(var.is_latch())
    {
      DATA_INVARIANT(var.bits.size() == 1, "");
      unsigned v=var.bits.front().current.var_no();
      literalt next=var.bits.front().next;

      out << "next" << v << " [shape=box,label=\""
          << dot_id(id2string(it->first)) << "'\"]" << '\n';

      if(next.is_constant())
        out << "TRUE";
      else
        out << next.var_no();

      out << " -> next" << v;
      if(next.sign()) out << " [arrowhead=odiamond]";
      out << '\n';
    }
  }
}
