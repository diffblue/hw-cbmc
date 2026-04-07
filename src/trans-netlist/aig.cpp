/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "aig.h"

#include <cassert>
#include <ostream>
#include <string>

aigt::reverse_labelingt aigt::reverse_labeling() const
{
  reverse_labelingt result;

  for(auto &[label, literal] : labeling)
  {
    auto &labels = result[literal.var_no()];
    if(!labels.empty())
      labels += ',';
    if(literal.sign())
      labels += '!';
    labels += label;
  }

  return result;
}

std::string aigt::label(
  literalt::var_not v,
  const reverse_labelingt &reverse_labeling) const
{
  auto labeling_it = reverse_labeling.find(v);
  if(labeling_it != reverse_labeling.end())
    return labeling_it->second;
  else
    return std::to_string(v);
}

void aigt::print(
  std::ostream &out,
  const reverse_labelingt &reverse_labeling,
  literalt a) const
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

  literalt::var_not node_nr = a.var_no();

  {
    const aig_nodet &node = nodes[node_nr];

    if(node.is_and())
    {
      if (a.sign())
        out << "!(";
      print(out, reverse_labeling, node.a);
      out << " & ";
      print(out, reverse_labeling, node.b);
      if (a.sign())
        out << ')';
    }
    else if(node.is_var())
    {
      if (a.sign())
        out << "!(";
      out << label(node_nr, reverse_labeling);
      if(a.sign())
        out << ')';
    }
    else
    {
      if (a.sign())
        out << "!";
      out << "unknown(" << node_nr << ")";
    }
  }
}

void aigt::output_dot_node(
  std::ostream &out,
  const reverse_labelingt &reverse_labeling,
  literalt::var_not v) const
{
  const aig_nodet &node = nodes[v];

  if(node.is_and())
  {
    out << v << " [label=\"" << label(v, reverse_labeling) << "\"]" << '\n';
    output_dot_edge(out, v, node.a);
    output_dot_edge(out, v, node.b);
  }
  else // the node is a terminal
  {
    out << v << " [label=\"" << label(v, reverse_labeling) << "\""
        << ",shape=box]" << '\n';
  }
}

void aigt::output_dot_edge(std::ostream &out, literalt::var_not v, literalt l)
  const
{
  if(l.is_true())
  {
    out << "TRUE -> " << v;
  }
  else if(l.is_false())
  {
    out << "TRUE -> " << v;
    out << " [arrowhead=odiamond]";
  }
  else
  {
    out << l.var_no() << " -> " << v;
    if (l.sign())
      out << " [arrowhead=odiamond]";
  }

  out << '\n';
}

void aigt::output_dot(std::ostream &out) const
{
  auto reverse_labeling = this->reverse_labeling();

  // constant TRUE
  out << "TRUE [label=\"TRUE\", shape=box]" << '\n';

  // now the nodes
  for (nodest::size_type n = 0; n < number_of_nodes(); n++)
    output_dot_node(out, reverse_labeling, n);
}

void aigt::print(std::ostream &out) const
{
  auto reverse_labeling = this->reverse_labeling();

  for (nodest::size_type n = 0; n < number_of_nodes(); n++) {
    out << "n" << n << " = ";
    literalt l;
    l.set(n, false);
    print(out, reverse_labeling, l);
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
