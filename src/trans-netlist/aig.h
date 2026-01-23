/*******************************************************************\

Module: AND-Inverter Graph

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// AND-Inverter Graph

#ifndef CPROVER_TRANS_NETLIST_AIG_H
#define CPROVER_TRANS_NETLIST_AIG_H

#include <map>
#include <set>
#include <vector>

#include <solvers/prop/literal.h>

class aig_nodet {
public:
  literalt a, b;

  explicit aig_nodet(literalt::var_not var_no)
    : a{literalt::unused_var_no(), false}, b{var_no, false}
  {
  }

  aig_nodet(literalt _a, literalt _b) : a(_a), b(_b)
  {
  }

  bool is_and() const
  {
    return a.var_no() != literalt::unused_var_no();
  }

  bool is_var() const
  {
    return a.var_no() == literalt::unused_var_no();
  }

  literalt::var_not var_no() const
  {
    PRECONDITION(is_var());
    return b.var_no();
  }
};

class aigt {
public:
  aigt() {}

  ~aigt() {}

  typedef aig_nodet nodet;
  typedef std::vector<nodet> nodest;

  // The nodes are expected to be in dependency order,
  // see check_ordering().
  nodest nodes;

  void clear() { nodes.clear(); }

  const aig_nodet &get_node(literalt l) const { return nodes[l.var_no()]; }

  aig_nodet &get_node(literalt l) { return nodes[l.var_no()]; }

  nodest::size_type number_of_nodes() const { return nodes.size(); }

  void swap(aigt &g) { nodes.swap(g.nodes); }

  literalt new_var_node(literalt::var_not var_no = literalt::unused_var_no())
  {
    nodes.emplace_back(var_no);
    return {narrow_cast<literalt::var_not>(nodes.size() - 1), false};
  }

  literalt new_and_node(literalt a, literalt b) {
    PRECONDITION(a.var_no() < number_of_nodes());
    PRECONDITION(b.var_no() < number_of_nodes());
    nodes.emplace_back(a, b);
    return {narrow_cast<literalt::var_not>(nodes.size() - 1), false};
  }

  bool empty() const { return nodes.empty(); }

  void print(std::ostream &out) const;
  void print(std::ostream &out, literalt a) const;
  void output_dot_node(std::ostream &out, nodest::size_type v) const;
  void output_dot_edge(std::ostream &out, nodest::size_type v,
                       literalt l) const;
  void output_dot(std::ostream &out) const;

  std::string label(nodest::size_type v) const;
  std::string dot_label(nodest::size_type v) const;

  /// Check that the nodes are in topological order,
  /// otherwise fails a DATA_INVARIANT.
  void check_ordering() const;
};

std::ostream &operator<<(std::ostream &, const aigt &);

class aig_plus_constraintst : public aigt {
public:
  typedef std::vector<literalt> constraintst;
  constraintst constraints;

  void clear() {
    aigt::clear();
    constraints.clear();
  }
};

#endif // CPROVER_TRANS_NETLIST_AIG_H
