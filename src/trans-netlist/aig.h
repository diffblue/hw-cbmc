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

  // a primary input
  aig_nodet()
    : a{literalt::unused_var_no(), false}, b{literalt::unused_var_no(), false}
  {
  }

  // an 'and' node
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

  bool is_input() const
  {
    return a.var_no() == literalt::unused_var_no();
  }
};

class aigt {
public:
  aigt() {}

  ~aigt() {}

  typedef aig_nodet nodet;
  typedef std::vector<nodet> nodest;

  // convenience constructor
  explicit aigt(std::initializer_list<nodet> _nodes) : nodes(_nodes)
  {
  }

  // factory for a primary input
  static nodet input_node()
  {
    return nodet{};
  }

  // factory for an 'and' node
  static nodet and_node(literalt a, literalt b)
  {
    return nodet{a, b};
  }

  // The nodes are expected to be in dependency order,
  // see check_ordering().
  nodest nodes;

  // An (optional) labeling, mapping labels to nodes or their negation.
  using labelingt = std::map<std::string, literalt>;
  labelingt labeling;

  void clear()
  {
    nodes.clear();
    labeling.clear();
  }

  const aig_nodet &get_node(literalt l) const { return nodes[l.var_no()]; }

  aig_nodet &get_node(literalt l) { return nodes[l.var_no()]; }

  nodest::size_type number_of_nodes() const { return nodes.size(); }

  void swap(aigt &g) { nodes.swap(g.nodes); }

  literalt new_input()
  {
    nodes.emplace_back();
    return {narrow_cast<literalt::var_not>(nodes.size() - 1), false};
  }

  literalt new_input(const std::string &_label)
  {
    auto l = new_input();
    label(l, _label);
    return l;
  }

  literalt new_var_node()
  {
    return new_input();
  }

  // label a node
  void label(literalt l, const std::string &label)
  {
    labeling[label] = l;
  }

  literalt new_and_node(literalt a, literalt b)
  {
    PRECONDITION(a.var_no() < number_of_nodes());
    PRECONDITION(b.var_no() < number_of_nodes());
    nodes.emplace_back(a, b);
    return {narrow_cast<literalt::var_not>(nodes.size() - 1), false};
  }

  bool empty() const { return nodes.empty(); }

  void print(std::ostream &) const;
  void output_dot(std::ostream &) const;

  /// Check that the nodes are in topological order,
  /// otherwise fails a DATA_INVARIANT.
  void check_ordering() const;

protected:
  using reverse_labelingt = std::map<literalt::var_not, std::string>;
  reverse_labelingt reverse_labeling() const;

  std::string label(literalt::var_not, const reverse_labelingt &) const;

  void print(std::ostream &out, const reverse_labelingt &, literalt) const;
  void output_dot_node(
    std::ostream &out,
    const reverse_labelingt &,
    literalt::var_not) const;
  void output_dot_edge(std::ostream &out, literalt::var_not, literalt l) const;
};

std::ostream &operator<<(std::ostream &, const aigt &);

class aig_plus_constraintst : public aigt
{
public:
  typedef std::vector<literalt> constraintst;
  constraintst constraints;

  // An equivalence between two nodes, given as literalt.
  // This avoids the need to re-discover functionally
  // equivalent nodes via SAT sweeping or the like.
  // The use of constants true/false is allowed.
  // These are redundantly stored as constraints as well.
  using equivalencet = std::pair<literalt, literalt>;
  using equivalencest = std::vector<equivalencet>;

  equivalencest equivalences;

  void clear()
  {
    aigt::clear();
    constraints.clear();
    equivalences.clear();
  }
};

#endif // CPROVER_TRANS_NETLIST_AIG_H
