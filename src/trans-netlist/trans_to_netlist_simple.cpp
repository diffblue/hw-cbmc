/*******************************************************************\

Module: Transition System represented by a Netlist

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "trans_to_netlist_simple.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/ebmc_util.h>
#include <util/expr_util.h>
#include <util/mathematical_expr.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include <ebmc/ebmc_error.h>
#include <solvers/flattening/boolbv_width.h>
#include <solvers/prop/literal_expr.h>
#include <temporal-logic/ctl.h>
#include <temporal-logic/ltl.h>
#include <temporal-logic/sva_to_ltl.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

#include "aig_prop.h"
#include "build_netlist_var_map.h"
#include "netlist.h"
#include "netlist_boolbv.h"

#include <algorithm>

/*******************************************************************\

   Class: convert_trans_to_netlist_simplet

 Purpose:

\*******************************************************************/

class convert_trans_to_netlist_simplet : public messaget
{
public:
  convert_trans_to_netlist_simplet(
    symbol_table_baset &_symbol_table,
    netlistt &_dest,
    message_handlert &_message_handler)
    : messaget(_message_handler),
      symbol_table(_symbol_table),
      ns(_symbol_table),
      dest(_dest),
      aig_prop(dest, _message_handler),
      solver(ns, aig_prop, _message_handler, dest.var_map)
  {
  }

  void operator()(
    const irep_idt &module,
    const transt &,
    const std::map<irep_idt, exprt> &properties);

protected:
  symbol_table_baset &symbol_table;
  const namespacet ns;
  netlistt &dest;
  aig_prop_constraintt aig_prop;
  netlist_boolbvt solver;

  static void allocate_nodes(netlistt &dest);
  std::optional<exprt> convert_property(const exprt &);
};

void convert_trans_to_netlist_simplet::operator()(
  const irep_idt &module,
  const transt &trans,
  const std::map<irep_idt, exprt> &properties)
{
  // identify the variables we want in the AIG
  dest.var_map = build_netlist_var_map(symbol_table, module);

  // allocate AIG nodes
  allocate_nodes(dest);

  // finish the var_map
  dest.var_map.build_reverse_map();

  // convert the initial state constraints
  dest.initial.push_back(solver.convert(trans.init()));

  // invar + trans
  solver.set_to_true(trans.invar());
  solver.set_to_true(trans.trans());

  // convert the properties
  for(const auto &[id, property_expr] : properties)
  {
    auto netlist_expr_opt = convert_property(property_expr);
    dest.properties.emplace(id, netlist_expr_opt);
  }

  // find the nondet nodes
  for(std::size_t n = 0; n < dest.nodes.size(); n++)
  {
    if(dest.nodes[n].is_var())
    {
      const var_mapt::reverse_mapt::const_iterator it =
        dest.var_map.reverse_map.find(n);

      if(it == dest.var_map.reverse_map.end())
        dest.var_map.record_as_nondet(n);
    }
  }

  // label the AIG nodes
  for(auto var_map_it : dest.var_map.sorted())
  {
    auto &var = var_map_it->second;

    for(std::size_t bit_nr = 0; bit_nr < var.bits.size(); bit_nr++)
    {
      std::string label = id2string(var_map_it->first);
      if(var.bits.size() != 1)
        label += '[' + std::to_string(bit_nr) + ']';

      dest.label(var.bits[bit_nr].current, label);

      if(var.has_next())
        dest.label(var.bits[bit_nr].next, label + '\'');
    }
  }
}

void convert_trans_to_netlist_simplet::allocate_nodes(netlistt &dest)
{
  // we work with the sorted var_map to get a deterministic allocation
  for(auto var_map_it : dest.var_map.sorted())
  {
    auto &var = var_map_it->second;

    for(auto &bit : var.bits)
    {
      bit.current = dest.new_var_node();

      // use a primary input as AIG node for the next state value
      if(var.has_next())
      {
        bit.next = dest.new_var_node();
        dest.var_map.record_as_nondet(bit.next.var_no());
      }
    }
  }
}

std::optional<exprt>
convert_trans_to_netlist_simplet::convert_property(const exprt &expr)
{
  if(is_temporal_operator(expr))
  {
    if(is_LTL_operator(expr) || is_CTL_operator(expr))
    {
      exprt copy = expr;
      for(auto &op : copy.operands())
      {
        auto op_opt = convert_property(op);
        if(op_opt.has_value())
          op = op_opt.value();
        else
          return {};
      }
      return copy;
    }
    else if(is_SVA_operator(expr))
    {
      // Try to turn into LTL
      try
      {
        auto LTL = SVA_to_LTL(expr);
        return convert_property(LTL);
      }
      catch(sva_to_ltl_unsupportedt)
      {
        return {};
      }
    }
    else
      return {};
  }
  else if(!has_temporal_operator(expr))
  {
    auto l = solver.convert(expr);
    return literal_exprt{l};
  }
  else if(
    expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_not ||
    expr.id() == ID_implies || expr.id() == ID_xor || expr.id() == ID_xnor ||
    (expr.id() == ID_equal && to_equal_expr(expr).lhs().type().id() == ID_bool))
  {
    exprt copy = expr;
    for(auto &op : copy.operands())
    {
      auto op_opt = convert_property(op);
      if(op_opt.has_value())
        op = op_opt.value();
      else
        return {};
    }
    return copy;
  }
  else
  {
    // contains temporal operator, but not propositional skeleton
    return {};
  }
}

void convert_trans_to_netlist_simple(
  symbol_table_baset &symbol_table,
  const irep_idt &module,
  const transt &trans_expr,
  const std::map<irep_idt, exprt> &properties,
  netlistt &dest,
  message_handlert &message_handler)
{
  convert_trans_to_netlist_simplet c(symbol_table, dest, message_handler);

  c(module, trans_expr, properties);
}
