/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef VHDL_PARSE_TREE_H
#define VHDL_PARSE_TREE_H

#include <list>
#include <set>

#include <util/hash_cont.h>
#include <util/string_hash.h>
#include <util/expr.h>

//#include "vhdl_module.h"

class vhdl_parse_treet
{
public:
  struct itemt
  {
  public:
    typedef enum { ARCHITECTURE, ENTITY, USE, LIBRARY } item_typet;
    item_typet type;
    
    irept name;
    
    bool is_architecture() const
    {
      return type==ARCHITECTURE;
    }

    bool is_entity() const
    {
      return type==ENTITY;
    }
    
    bool is_use() const
    {
      return type==USE;
    }
    
    bool is_library() const
    {
      return type==LIBRARY;
    }
    
    void show(std::ostream &out) const;
    static std::string pretty_name(const irept &);
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

  #if 0  
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
  #endif
  
  void swap(vhdl_parse_treet &parse_tree)
  {
    parse_tree.items.swap(items);
    parse_tree.expr.swap(expr);
    parse_tree.module_map.swap(module_map);
  }

  #if 0
  void modules_provided(
    std::set<std::string> &module_set) const;
  #endif

  typedef hash_map_cont<irep_idt, itemst::iterator, irep_id_hash> module_mapt;
  module_mapt module_map;
  
  void build_module_map();
  
  void show(std::ostream &out) const;
};

#endif
