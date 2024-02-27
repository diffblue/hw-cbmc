/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_PARSE_TREE_H
#define CPROVER_VERILOG_PARSE_TREE_H

#include <list>
#include <set>

#include <util/string_hash.h>

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
      out << "Typedef:\n";
      out << "\n";
    }
  };

  struct itemt
  {
  public:
    typedef enum
    {
      CLASS,
      INTERFACE,
      MODULE,
      PACKAGE,
      PRIMITIVE,
      PROGRAM,
      TYPEDEF
    } item_typet;
    item_typet type;

    explicit itemt(item_typet __type) : type(__type)
    {
    }

    verilog_modulet verilog_module;
    
    verilog_typedeft verilog_typedef;

    source_locationt source_location;

    bool is_class() const
    {
      return type == CLASS;
    }

    bool is_interface() const
    {
      return type == INTERFACE;
    }

    bool is_module() const
    {
      return type==MODULE;
    }

    bool is_package() const
    {
      return type == PACKAGE;
    }

    bool is_primitive() const
    {
      return type == PRIMITIVE;
    }

    bool is_program() const
    {
      return type == PROGRAM;
    }

    bool is_typedef() const
    {
      return type==TYPEDEF;
    }

    void show(std::ostream &) const;
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

  void create_class(exprt &name);

  void create_interface(exprt &name);

  void create_module(
    irept &attributes,
    irept &module_keyword,
    exprt &name,
    exprt &parameter_port_list,
    exprt &ports,
    exprt &statements);

  void create_package(exprt &name);

  void create_primitive(exprt &name);

  void create_program(exprt &name);

  void create_typedef(irept &declaration)
  {
    items.emplace_back(itemt::TYPEDEF);
    items.back().verilog_typedef.symbol.swap(declaration.get_sub()[0]);
    items.back().verilog_typedef.type.swap(declaration.add(ID_type));
  }
  
  void swap(verilog_parse_treet &parse_tree)
  {
    parse_tree.items.swap(items);
    parse_tree.expr.swap(expr);
    parse_tree.module_map.swap(module_map);
  }

  void modules_provided(
    std::set<std::string> &module_set) const;

  typedef std::unordered_map<irep_idt, itemst::iterator, irep_id_hash> module_mapt;
  module_mapt module_map;
  
  void build_module_map();
  
  void show(std::ostream &out) const;
};

#endif
