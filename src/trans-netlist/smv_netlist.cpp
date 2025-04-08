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

  for(std::size_t i = 0; i < id.size(); i++)
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

  std::size_t node_nr = a.var_no();
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

  class expr2smv_netlistt : public expr2smvt
  {
  public:
    expr2smv_netlistt(const namespacet &ns, const netlistt &__netlist)
      : expr2smvt(ns), netlist(__netlist)
    {
    }

  protected:
    const netlistt &netlist;

    resultt convert_rec(const exprt &expr) override
    {
      if(expr.id() == ID_literal)
      {
        std::ostringstream buffer;
        auto l = to_literal_expr(expr).get_literal();
        print_smv(netlist, buffer, l);
        if(l.sign())
          return {precedencet::NOT, buffer.str()};
        else
          return {precedencet::MAX, buffer.str()};
      }
      else
        return expr2smvt::convert_rec(expr);
    }
  };

  out << expr2smv_netlistt{ns, netlist}.convert(expr);
}

void smv_netlist(const netlistt &netlist, std::ostream &out)
{
  out << "MODULE main" << '\n';

  out << '\n';
  out << "-- Variables" << '\n';
  out << '\n';

  auto &var_map = netlist.var_map;

  for(auto &var_it : var_map.map)
  {
    const var_mapt::vart &var = var_it.second;

    for(std::size_t i = 0; i < var.bits.size(); i++)
    {
      if(var.is_latch())
      {
        out << "VAR " << id2smv(var_it.first);
        if(var.bits.size() != 1)
          out << "[" << i << "]";
        out << ": boolean;" << '\n';
      }
    }
  }

  out << '\n';
  out << "-- Inputs" << '\n';
  out << '\n';

  for(auto &var_it : var_map.map)
  {
    const var_mapt::vart &var = var_it.second;

    for(std::size_t i = 0; i < var.bits.size(); i++)
    {
      if(var.is_input())
      {
        out << "VAR " << id2smv(var_it.first);
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

  for(std::size_t node_nr = 0; node_nr < nodes.size(); node_nr++)
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

  for(auto &var_it : var_map.map)
  {
    const var_mapt::vart &var = var_it.second;

    for(std::size_t i = 0; i < var.bits.size(); i++)
    {
      if(var.is_latch())
      {
        out << "ASSIGN next(" << id2smv(var_it.first);
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
      // Should have been mapped to LTL
      DATA_INVARIANT(false, "smv_netlist got SVA");
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
