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

void print_smv(
  const netlistt &netlist,
  const std::map<literalt::var_not, std::string> &variable_names,
  std::ostream &out,
  literalt a)
{
  if(a == const_literal(false))
  {
    out << "FALSE";
    return;
  }
  else if(a == const_literal(true))
  {
    out << "TRUE";
    return;
  }

  auto node_nr = a.var_no();
  DATA_INVARIANT(node_nr < netlist.number_of_nodes(), "node_nr in range");

  if(a.sign())
    out << "!";

  auto &nodes = netlist.nodes;

  if(nodes[node_nr].is_and())
    out << "node" << node_nr;
  else if(nodes[node_nr].is_var())
  {
    auto name_it = variable_names.find(node_nr);
    DATA_INVARIANT(
      name_it != variable_names.end(), "AIG variable node must have name");
    out << name_it->second;
  }
  else
    out << "unknown";
}

void print_smv(
  const netlistt &netlist,
  const std::map<literalt::var_not, std::string> &variable_names,
  std::ostream &out,
  const exprt &expr)
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  class expr2smv_netlistt : public expr2smvt
  {
  public:
    expr2smv_netlistt(
      const namespacet &ns,
      const netlistt &__netlist,
      const std::map<literalt::var_not, std::string> &_variable_names)
      : expr2smvt(ns), netlist(__netlist), variable_names(_variable_names)
    {
    }

  protected:
    const netlistt &netlist;
    const std::map<literalt::var_not, std::string> &variable_names;

    resultt convert_rec(const exprt &expr) override
    {
      if(expr.id() == ID_literal)
      {
        std::ostringstream buffer;
        auto l = to_literal_expr(expr).get_literal();
        print_smv(netlist, variable_names, buffer, l);
        if(l.sign() && !l.is_constant())
          return {precedencet::NOT, buffer.str()};
        else
          return {precedencet::MAX, buffer.str()};
      }
      else
        return expr2smvt::convert_rec(expr);
    }
  };

  out << expr2smv_netlistt{ns, netlist, variable_names}.convert(expr);
}

void smv_netlist(const netlistt &netlist, std::ostream &out)
{
  out << "MODULE main" << '\n';

  // We use the sorted var map to get deterministic output
  auto &var_map = netlist.var_map;
  const auto sorted_var_map = var_map.sorted();
  std::map<literalt::var_not, std::string> variable_names;

  auto declare_var =
    [&variable_names](var_mapt::mapt::const_iterator var_it, std::ostream &out)
  {
    const var_mapt::vart &var = var_it->second;
    for(std::size_t i = 0; i < var.bits.size(); i++)
    {
      std::string name = id2smv(var_it->first);
      if(var_it->second.bits.size() != 1)
        name += '[' + std::to_string(i) + ']';
      variable_names[var.bits[i].current.var_no()] = name;
      out << "VAR " << name << ": boolean;" << '\n';
    }
  };

  out << '\n';
  out << "-- Variables" << '\n';
  out << '\n';

  for(auto var_it : sorted_var_map)
  {
    if(var_it->second.is_latch())
      declare_var(var_it, out);
  }

  out << '\n';
  out << "-- Inputs" << '\n';
  out << '\n';

  for(auto var_it : sorted_var_map)
  {
    if(var_it->second.is_input())
      declare_var(var_it, out);
  }

  out << '\n';
  out << "-- Nondeterministic nodes" << '\n';
  out << '\n';

  for(auto var_it : sorted_var_map)
  {
    if(var_it->second.is_nondet())
      declare_var(var_it, out);
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
      print_smv(netlist, variable_names, out, node.a);
      out << " & ";
      print_smv(netlist, variable_names, out, node.b);
      out << ";" << '\n';
    }
  }

  out << '\n';
  out << "-- Next state functions" << '\n';
  out << '\n';

  for(auto var_it : sorted_var_map)
  {
    const var_mapt::vart &var = var_it->second;

    for(std::size_t i = 0; i < var.bits.size(); i++)
    {
      if(var.is_latch())
      {
        out << "ASSIGN next(" << id2smv(var_it->first);
        if(var.bits.size() != 1)
          out << "[" << i << "]";
        out << "):=";
        print_smv(netlist, variable_names, out, var.bits[i].next);
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
      print_smv(netlist, variable_names, out, initial_l);
      out << '\n';
    }
  }

  out << '\n';
  out << "-- in-state constraints" << '\n';
  out << '\n';

  for(auto &constraint_l : netlist.constraints)
  {
    if(!constraint_l.is_true())
    {
      out << "INVAR ";
      print_smv(netlist, variable_names, out, constraint_l);
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
      print_smv(netlist, variable_names, out, trans_l);
      out << '\n';
    }
  }

  out << '\n';
  out << "-- Properties" << '\n';
  out << '\n';

  for(auto &[id, netlist_expr] : netlist.properties)
  {
    if(!netlist_expr.has_value())
    {
      // translation has failed
      out << "-- " << id << '\n';
      out << "-- not translated\n";
      out << '\n';
    }
    else if(is_CTL(*netlist_expr))
    {
      out << "-- " << id << '\n';
      out << "CTLSPEC ";
      print_smv(netlist, variable_names, out, *netlist_expr);
      out << '\n';
    }
    else if(is_LTL(*netlist_expr))
    {
      out << "-- " << id << '\n';
      out << "LTLSPEC ";
      print_smv(netlist, variable_names, out, *netlist_expr);
      out << '\n';
    }
    else if(is_SVA(*netlist_expr))
    {
      // Should have been mapped to LTL
      DATA_INVARIANT(false, "smv_netlist got SVA");
    }
    else
    {
      // translated to something we can't print
      out << "-- " << id << '\n';
      out << "-- cannot output\n";
      out << '\n';
    }
  }
}
