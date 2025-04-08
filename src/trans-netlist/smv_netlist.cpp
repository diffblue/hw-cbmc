/*******************************************************************\

Module: SMV Netlists

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "smv_netlist.h"
#include <smvlang/expr2smv_class.h>

#include <util/namespace.h>
#include <util/symbol_table.h>

#include <solvers/prop/literal_expr.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

std::string id2smv(const irep_idt &id)
{
  std::string result;

  for(unsigned i = 0; i < id.size(); i++)
  {
    const bool first = i == 0;
    char ch = id[i];
    if(
      isalnum(ch) || ch == '_' || (ch == '.' && !first) ||
      (ch == '#' && !first) || (ch == '-' && !first))
    {
      result += ch;
    }
    else if(ch == ':')
    {
      result += '.';
      if((i - 1) < id.size() && id[i + 1] == ':')
        i++;
    }
    else
    {
      result += '$';
      result += std::to_string(ch);
      result += '$';
    }
  }

  return result;
}

void print_smv(const netlistt &netlist, std::ostream &out, literalt a)
{
  if(a == const_literal(false))
  {
    out << "0";
    return;
  }
  else if(a == const_literal(true))
  {
    out << "1";
    return;
  }

  unsigned node_nr = a.var_no();
  DATA_INVARIANT(node_nr < netlist.number_of_nodes(), "node_nr in range");

  if(a.sign())
    out << "!";

  auto &nodes = netlist.nodes;

  if(nodes[node_nr].is_and())
    out << "node" << node_nr;
  else if(nodes[node_nr].is_var())
  {
    const bv_varidt &varid = netlist.var_map.reverse(node_nr);
    out << id2smv(varid.id);
    const var_mapt::mapt::const_iterator v_it =
      netlist.var_map.map.find(varid.id);
    if(v_it != netlist.var_map.map.end() && v_it->second.bits.size() != 1)
      out << '[' << varid.bit_nr << ']';
  }
  else
    out << "unknown";
}

void print_smv(const netlistt &netlist, std::ostream &out, const exprt &expr)
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  // replace literal expressions by symbols

  exprt replaced = expr;
  replaced.visit_pre(
    [&netlist](exprt &node)
    {
      if(node.id() == ID_literal)
      {
        std::ostringstream buffer;
        print_smv(netlist, buffer, to_literal_expr(node).get_literal());
        node = symbol_exprt{buffer.str(), node.type()};
      }
    });

  out << expr2smv(replaced, ns);
}

void smv_netlist(const netlistt &netlist, std::ostream &out)
{
  out << "MODULE main" << '\n';

  out << '\n';
  out << "-- Variables" << '\n';
  out << '\n';

  auto &var_map = netlist.var_map;

  for(var_mapt::mapt::const_iterator it = var_map.map.begin();
      it != var_map.map.end();
      it++)
  {
    const var_mapt::vart &var = it->second;

    for(unsigned i = 0; i < var.bits.size(); i++)
    {
      if(var.is_latch())
      {
        out << "VAR " << id2smv(it->first);
        if(var.bits.size() != 1)
          out << "[" << i << "]";
        out << ": boolean;" << '\n';
      }
    }
  }

  out << '\n';
  out << "-- Inputs" << '\n';
  out << '\n';

  for(var_mapt::mapt::const_iterator it = var_map.map.begin();
      it != var_map.map.end();
      it++)
  {
    const var_mapt::vart &var = it->second;

    for(unsigned i = 0; i < var.bits.size(); i++)
    {
      if(var.is_input())
      {
        out << "VAR " << id2smv(it->first);
        if(var.bits.size() != 1)
          out << "[" << i << "]";
        out << ": boolean;" << '\n';
      }
    }
  }

  out << '\n';
  out << "-- AND Nodes" << '\n';
  out << '\n';

  auto &nodes = netlist.nodes;

  for(unsigned node_nr = 0; node_nr < nodes.size(); node_nr++)
  {
    const aig_nodet &node = nodes[node_nr];

    if(node.is_and())
    {
      out << "DEFINE node" << node_nr << ":=";
      print_smv(netlist, out, node.a);
      out << " & ";
      print_smv(netlist, out, node.b);
      out << ";" << '\n';
    }
  }

  out << '\n';
  out << "-- Next state functions" << '\n';
  out << '\n';

  for(var_mapt::mapt::const_iterator it = var_map.map.begin();
      it != var_map.map.end();
      it++)
  {
    const var_mapt::vart &var = it->second;

    for(unsigned i = 0; i < var.bits.size(); i++)
    {
      if(var.is_latch())
      {
        out << "ASSIGN next(" << id2smv(it->first);
        if(var.bits.size() != 1)
          out << "[" << i << "]";
        out << "):=";
        print_smv(netlist, out, var.bits[i].next);
        out << ";" << '\n';
      }
    }
  }

  out << '\n';
  out << "-- Initial state" << '\n';
  out << '\n';

  for(auto &initial_l : netlist.initial)
  {
    if(!initial_l.is_true())
    {
      out << "INIT ";
      print_smv(netlist, out, initial_l);
      out << '\n';
    }
  }

  out << '\n';
  out << "-- TRANS" << '\n';
  out << '\n';

  for(auto &trans_l : netlist.transition)
  {
    if(!trans_l.is_true())
    {
      out << "TRANS ";
      print_smv(netlist, out, trans_l);
      out << '\n';
    }
  }

  out << '\n';
  out << "-- Properties" << '\n';
  out << '\n';

  for(auto &[id, netlist_expr] : netlist.properties)
  {
    if(is_CTL(netlist_expr))
    {
      out << "-- " << id << '\n';
      out << "CTLSPEC ";
      print_smv(netlist, out, netlist_expr);
      out << '\n';
    }
    else if(is_LTL(netlist_expr))
    {
      out << "-- " << id << '\n';
      out << "LTLSPEC ";
      print_smv(netlist, out, netlist_expr);
      out << '\n';
    }
    else if(is_SVA(netlist_expr))
    {
      if(is_SVA_always_p(netlist_expr))
      {
        out << "-- " << id << '\n';
        out << "CTLSPEC AG ";
        print_smv(netlist, out, to_sva_always_expr(netlist_expr).op());
        out << '\n';
      }
      else if(is_SVA_always_s_eventually_p(netlist_expr))
      {
        out << "-- " << id << '\n';
        out << "CTLSPEC AG AF ";
        print_smv(
          netlist,
          out,
          to_sva_s_eventually_expr(to_sva_always_expr(netlist_expr).op()).op());
        out << '\n';
      }
      else
      {
        out << "-- " << id << '\n';
        out << "-- not translated\n";
        out << '\n';
      }
    }
    else
    {
      // neither LTL nor CTL nor SVA
      out << "-- " << id << '\n';
      out << "-- not translated\n";
      out << '\n';
    }
  }
}
