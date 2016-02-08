/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VHDL_PARSE_TREE_H
#define CPROVER_VHDL_PARSE_TREE_H

#include <list>
#include <set>

#include <util/hash_cont.h>
#include <util/string_hash.h>
#include <util/expr.h>

//#include "vhdl_module.h"

class vhdl_parse_treet
{
public:
  struct itemt:public exprt
  {
  public:
    irep_idt get_item_type() const { return get("item_type"); }
    void set_item_type(const irep_idt &item_type) { set("item_type", item_type); }

    void set_name(const irept &name) { set(ID_name, name); }    
    irept get_name() const { return find(ID_name); }
    
    void show(std::ostream &out) const;
    static std::string pretty_name(const irept &);
    std::string get_pretty_name() const { return pretty_name(get_name()); }
    
    bool is_architecture() const { return get("item_type")=="architecture"; }
    bool is_entity() const { return get("item_type")=="entity"; }
    bool is_use() const { return get("item_type")=="use"; }
    bool is_library() const { return get("item_type")=="library"; }
  };
  
  typedef std::list<itemt> itemst;
  itemst items;
  
  void clear()
  {
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
