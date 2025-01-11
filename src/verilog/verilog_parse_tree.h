/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_PARSE_TREE_H
#define CPROVER_VERILOG_PARSE_TREE_H

#include <util/string_hash.h>

#include "verilog_expr.h"
#include "verilog_standard.h"

#include <list>
#include <set>

class verilog_parse_treet
{
public:
  explicit verilog_parse_treet(verilog_standardt _standard)
    : standard(_standard)
  {
  }

  verilog_standardt standard;

  using itemt = irept;

  void show(const itemt &, std::ostream &) const;

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
    return item_map.count(name) != 0;
  }

  static exprt create_module(
    irept &attributes,
    irept &module_keyword,
    exprt &name,
    exprt &parameter_port_list,
    exprt &ports,
    exprt &statements);

  itemt &add_item(itemt item)
  {
    items.push_back(std::move(item));
    return items.back();
  }
  
  void swap(verilog_parse_treet &parse_tree)
  {
    parse_tree.items.swap(items);
    parse_tree.expr.swap(expr);
    parse_tree.item_map.swap(item_map);
    std::swap(parse_tree.standard, standard);
  }

  void modules_provided(
    std::set<std::string> &module_set) const;

  // An index into the items list.
  // The key is
  //   package::name for packages
  //   name          for modules, etc.
  // as packages have a separate name space (1800-2017 3.13).
  typedef std::
    unordered_map<irep_idt, const verilog_item_containert *, irep_id_hash>
      item_mapt;
  item_mapt item_map;

  void build_item_map();

  void show(std::ostream &out) const;
};

#endif
