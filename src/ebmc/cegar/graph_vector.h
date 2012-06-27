/*******************************************************************\

Module: Template Class for Graphs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EBMC_GRAPH_VECTOR_H
#define CPROVER_EBMC_GRAPH_VECTOR_H

#include <set>
#include <vector>

class graph_vector_nodet
{
public:
  // edges
  typedef std::set<unsigned> edgest;
  edgest in, out;
  
  bool marked;
  graph_vector_nodet():marked(false) { }
};

template<class nodet>
class graph_vectort
{
public:
  void add_edge(unsigned from, unsigned to)
  {
    assert(from<nodes.size());
    assert(to<nodes.size());
    nodes[from].out.insert(to);
    nodes[to].in.insert(from);
  }
  
  bool has_edge(unsigned from, unsigned to) const
  {
    assert(from<nodes.size());
    const nodet &from_node=nodes[from];
    return from_node.out.find(to)!=from_node.out.end();
  }
  
  void remove_edge(unsigned from, unsigned to)
  {
    assert(from<nodes.size());
    assert(to<nodes.size());
    nodes[from].out.erase(to);
    nodes[to].in.erase(from);
  }
  
  typedef std::vector<nodet> nodest;
  nodest nodes;
  
  typedef std::set<unsigned> node_sett;
  node_sett node_set;
  
  unsigned add_node()
  {
    unsigned v=nodes.size();
    nodes.resize(v+1);
    node_set.insert(v);
    return v;
  }
  
  void mark(unsigned v)
  {
    assert(v<nodes.size());
    nodes[v].marked=true;
  }
  
  void unmark()
  {
    for(typename nodest::iterator it=nodes.begin();
        it!=nodes.end();
        it++)
      it->marked=false;
  }
  
  void delete_node(unsigned v)
  {
    assert(v<nodes.size());
    node_set.erase(v);
    nodet &node_v=nodes[v];

    for(typename nodet::edgest::const_iterator it=node_v.in.begin();
        it!=node_v.in.end();
        it++)
    {
      unsigned w=*it;
      assert(w<nodes.size());
      nodet &node_w=nodes[w];
      node_w.out.erase(w);
    }

    for(typename nodet::edgest::const_iterator it=node_v.out.begin();
        it!=node_v.out.end();
        it++)
    {
      unsigned w=*it;
      assert(w<nodes.size());
      nodet &node_w=nodes[w];
      node_w.in.erase(w);
    }
    
    node_v.in.clear();
    node_v.out.clear();
  }
};

#endif
