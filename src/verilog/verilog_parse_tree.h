/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef VERILOG_PARSE_TREE_H
#define VERILOG_PARSE_TREE_H

#include <list>
#include <set>

#include <hash_cont.h>
#include <string_hash.h>

#include "verilog_module.h"

class verilog_parse_treet
{
public:
  class verilog_typedeft
  {
  public:
    typet symbol;
    typet type;
    
    void show(std::ostream &out) const
    {
      out << "Typedef: " << std::endl;
      out << std::endl;
    }
  };

  struct itemt
  {
  public:
    typedef enum { MODULE, TYPEDEF } item_typet;
    item_typet type;
    
    verilog_modulet verilog_module;
    
    verilog_typedeft verilog_typedef;
    
    bool is_module() const
    {
      return type==MODULE;
    }

    bool is_typedef() const
    {
      return type==TYPEDEF;
    }
    
    void show(std::ostream &out) const;
  };
  
  typedef std::list<itemt> itemst;
  itemst items;

  // for parsing expressions
  exprt expr;
  
  void clear()
  {
    expr.clear();
    items.clear();
  }
  
  bool has_module(const std::string &name) const
  {
    return module_map.count(name)!=0;
  }
  
  void create_module(
    irept &attributes,
    irept &module_keyword,
    exprt &name,
    exprt &ports,
    exprt &statements);

  void create_typedef(irept &type, irept &symbol)
  {
    items.push_back(itemt());
    items.back().type=itemt::TYPEDEF;
    items.back().verilog_typedef.symbol.swap(symbol);
    items.back().verilog_typedef.type.swap(type);
  }
  
  void swap(verilog_parse_treet &parse_tree)
  {
    parse_tree.items.swap(items);
    parse_tree.expr.swap(expr);
    parse_tree.module_map.swap(module_map);
  }

  void modules_provided(
    std::set<std::string> &module_set) const;

  typedef hash_map_cont<irep_idt, itemst::iterator, irep_id_hash> module_mapt;
  module_mapt module_map;
  
  void build_module_map();
  
  void show(std::ostream &out) const;
};

#endif
