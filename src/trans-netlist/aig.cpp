/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "aig.h"

#include <cassert>
#include <ostream>
#include <string>

std::string aigt::label(nodest::size_type v) const {
  return "var(" + std::to_string(v) + ")";
}

std::string aigt::dot_label(nodest::size_type v) const {
  return "var(" + std::to_string(v) + ")";
}

void aigt::print(std::ostream &out, literalt a) const {
  if (a == const_literal(false)) {
    out << "FALSE";
    return;
  } else if (a == const_literal(true)) {
    out << "TRUE";
    return;
  }

  literalt::var_not node_nr = a.var_no();

  {
    const aig_nodet &node = nodes[node_nr];

    if (node.is_and()) {
      if (a.sign())
        out << "!(";
      print(out, node.a);
      out << " & ";
      print(out, node.b);
      if (a.sign())
        out << ")";
    } else if (node.is_var()) {
      if (a.sign())
        out << "!";
      out << label(node_nr);
    } else {
      if (a.sign())
        out << "!";
      out << "unknown(" << node_nr << ")";
    }
  }
}

void aigt::output_dot_node(std::ostream &out, nodest::size_type v) const {
  const aig_nodet &node = nodes[v];

  if (node.is_and()) {
    out << v << " [label=\"" << v << "\"]"
        << "\n";
    output_dot_edge(out, v, node.a);
    output_dot_edge(out, v, node.b);
  } else // the node is a terminal
  {
    out << v << " [label=\"" << dot_label(v) << "\""
        << ",shape=box]"
        << "\n";
  }
}

void aigt::output_dot_edge(std::ostream &out, nodest::size_type v,
                           literalt l) const {
  if (l.is_true()) {
    out << "TRUE -> " << v;
  } else if (l.is_false()) {
    out << "TRUE -> " << v;
    out << " [arrowhead=odiamond]";
  } else {
    out << l.var_no() << " -> " << v;
    if (l.sign())
      out << " [arrowhead=odiamond]";
  }

  out << "\n";
}

void aigt::output_dot(std::ostream &out) const {
  // constant TRUE
  out << "TRUE [label=\"TRUE\", shape=box]"
      << "\n";

  // now the nodes
  for (nodest::size_type n = 0; n < number_of_nodes(); n++)
    output_dot_node(out, n);
}

void aigt::print(std::ostream &out) const {
  for (nodest::size_type n = 0; n < number_of_nodes(); n++) {
    out << "n" << n << " = ";
    literalt l;
    l.set(n, false);
    print(out, l);
    out << "\n";
  }
}

std::ostream &operator<<(std::ostream &out, const aigt &aig) {
  aig.print(out);
  return out;
}

void aigt::check_ordering() const
{
  for(std::size_t node_index = 0; node_index < nodes.size(); node_index++)
  {
    auto &node = nodes[node_index];
    if(node.is_and())
    {
      DATA_INVARIANT(node.a.var_no() < node_index, "aig topsort failure");
      DATA_INVARIANT(node.b.var_no() < node_index, "aig topsort failure");
    }
  }
}
