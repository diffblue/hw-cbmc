/*******************************************************************\

Module: Graph representing Netlist

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ctype.h>

#include <i2string.h>

#include <solvers/flattening/boolbv_width.h>

#include "netlist.h"

/*******************************************************************\

Function: netlistt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void netlistt::print(std::ostream &out) const
{
  var_map.output(out);

  out << std::endl;
  out << "Next state functions:" << std::endl;

  for(var_mapt::mapt::const_iterator
      it=var_map.map.begin();
      it!=var_map.map.end(); it++)
  {
    const var_mapt::vart &var=it->second;

    for(unsigned i=0; i<var.bits.size(); i++)
    {
      if(var.vartype==var_mapt::vart::VAR_LATCH)
      {
        out << "  NEXT(" << it->first;
        if(var.bits.size()!=1) out << "[" << i << "]";
        out << ")=";

        print(out, var.bits[i].next);

        out << std::endl;
      }
    }
  }

  out << std::endl;

  out << "Initial state: " << std::endl;

  for(unsigned i=0; i<initial.size(); i++)
  {
    out << "  ";
    print(out, initial[i]);
    out << std::endl;
  }

  out << std::endl;

  out << "Transition constraints: " << std::endl;

  for(unsigned i=0; i<transition.size(); i++)
  {
    out << "  ";
    print(out, transition[i]);
    out << std::endl;
  }
  
  out << std::endl;

  for(unsigned i=0; i<properties.size(); i++)
  {
    out << "Property " << (i+1) << ": ";
    print(out, properties[i]);
    out << std::endl;
  }
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
  assert(v<number_of_nodes());
  assert(nodes[v].is_var());
  const bv_varidt &varid=var_map.reverse(v);
  const var_mapt::mapt::const_iterator v_it=var_map.map.find(varid.id);
  if(v_it!=var_map.map.end() && v_it->second.bits.size()!=1)
    return id2string(varid.id)+'['+i2string(varid.bit_nr)+']';
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

  // add the sinks
  for(var_mapt::mapt::const_iterator
      it=var_map.map.begin();
      it!=var_map.map.end();
      it++)
  {
    const var_mapt::vart &var=it->second;

    if(var.vartype==var_mapt::vart::VAR_LATCH)
    {
      assert(var.bits.size()==1);
      unsigned v=var.bits.front().current.var_no();
      literalt next=var.bits.front().next;

      out << "next" << v << " [shape=box,label=\""
          << dot_id(id2string(it->first)) << "'\"]" << std::endl;

      if(next.is_constant())
        out << "TRUE";
      else
        out << next.var_no();

      out << " -> next" << v;
      if(next.sign()) out << " [arrowhead=odiamond]";
      out << std::endl;
    }
  }
}

/*******************************************************************\

Function: netlistt::output_smv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void netlistt::output_smv(std::ostream &out) const
{
  out << "MODULE main" << std::endl;

  out << std::endl;
  out << "-- Variables" << std::endl;
  out << std::endl;

  for(var_mapt::mapt::const_iterator
      it=var_map.map.begin();
      it!=var_map.map.end();
      it++)
  {
    const var_mapt::vart &var=it->second;

    for(unsigned i=0; i<var.bits.size(); i++)
    {
      if(var.is_latch())
      {
        out << "VAR " << id2smv(it->first);
        if(var.bits.size()!=1) out << "[" << i << "]";
        out << ": boolean;" << std::endl;
      }
    }
  }

  out << std::endl;
  out << "-- Inputs" << std::endl;
  out << std::endl;

  for(var_mapt::mapt::const_iterator
      it=var_map.map.begin();
      it!=var_map.map.end();
      it++)
  {
    const var_mapt::vart &var=it->second;

    for(unsigned i=0; i<var.bits.size(); i++)
    {
      if(var.is_input())
      {
        out << "VAR " << id2smv(it->first);
        if(var.bits.size()!=1) out << "[" << i << "]";
        out << ": boolean;" << std::endl;
      }
    }
  }

  out << std::endl;
  out << "-- AND Nodes" << std::endl;
  out << std::endl;

  for(unsigned node_nr=0; node_nr<nodes.size(); node_nr++)
  {
    const aig_nodet &node=nodes[node_nr];

    if(node.type==aig_nodet::AND)
    {
      out << "DEFINE node" << node_nr << ":=";
      print_smv(out, node.a);
      out << " & ";
      print_smv(out, node.b);
      out << ";" << std::endl;
    }
  }

  out << std::endl;
  out << "-- Next state functions" << std::endl;
  out << std::endl;

  for(var_mapt::mapt::const_iterator
      it=var_map.map.begin();
      it!=var_map.map.end();
      it++)
  {
    const var_mapt::vart &var=it->second;

    for(unsigned i=0; i<var.bits.size(); i++)
    {
      if(var.vartype==var_mapt::vart::VAR_LATCH)
      {
        out << "ASSIGN next(" << id2smv(it->first);
        if(var.bits.size()!=1) out << "[" << i << "]";
        out << "):=";
        print_smv(out, var.bits[i].next);
        out << ";" << std::endl;
      }
    }
  }

  out << std::endl;
  out << "-- Initial state" << std::endl;
  out << std::endl;

  for(unsigned i=0; i<initial.size(); i++)
  {
    out << "INIT ";
    print_smv(out, initial[i]);
    out << std::endl;
  }

  out << std::endl;
  out << "-- TRANS" << std::endl;
  out << std::endl;

  for(unsigned i=0; i<transition.size(); i++)
  {
    out << "TRANS ";
    print_smv(out, transition[i]);
    out << std::endl;
  }

  out << std::endl;
  out << "-- Properties" << std::endl;
  out << std::endl;
  
  for(unsigned i=0; i<properties.size(); i++)
  {
    out << "SPEC AG ";
    print_smv(out, properties[i]);
    out << std::endl;
  }
}

/*******************************************************************\

Function: netlistt::id2smv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string netlistt::id2smv(const irep_idt &id)
{
  std::string result;
  
  for(unsigned i=0; i<id.size(); i++)
  {
    char ch=id[i];
    if(isalnum(ch) || ch=='_' || ch=='.' || ch=='#')
      result+=ch;
    else if(ch==':')
    {
      result+='.';
      if((i-1)<id.size() && id[i+1]==':') i++;
    }
    else
    {
      result+='$';
      result+=i2string(ch);
      result+='$';
    }
  }
  
  return result;
}

/*******************************************************************\

Function: netlistt::print_smv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void netlistt::print_smv(
  std::ostream& out,
  literalt a) const
{
  if(a==const_literal(false))
  {
    out << "0";
    return;
  }
  else if(a==const_literal(true))
  {
    out << "1";
    return;
  }

  unsigned node_nr=a.var_no();
  assert(node_nr<number_of_nodes());

  if(a.sign()) out << "!";

  switch(nodes[node_nr].type)
  {
  case aig_nodet::AND:
    out << "node" << node_nr;
    break;
    
  case aig_nodet::VAR:
    {
      const bv_varidt &varid=var_map.reverse(node_nr);
      out << id2smv(varid.id);
      const var_mapt::mapt::const_iterator v_it=var_map.map.find(varid.id);
      if(v_it!=var_map.map.end() && v_it->second.bits.size()!=1)
        out << '[' << varid.bit_nr << ']';
    }
    break;
    
  default:
    out << "unknown";
  }
}

