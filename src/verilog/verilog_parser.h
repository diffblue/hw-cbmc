/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef VERILOG_PARSER_H
#define VERILOG_PARSER_H

#include <util/mp_arith.h>
#include <util/optional.h>
#include <util/parser.h>

#include "verilog_parse_tree.h"

#include <map>
#include <string>

int yyverilogparse();

class verilog_parsert:public parsert
{
public:
  verilog_parse_treet parse_tree;

  // for lexing strings
  std::string string_literal;
  
  typedef enum { LANGUAGE, EXPRESSION, TYPE } grammart;
  grammart grammar;
  
  typedef enum { STRICT_VERILOG, VIS_VERILOG, SYSTEM_VERILOG } modet;
  modet mode;
  
  virtual bool parse()
  {
    return yyverilogparse()!=0;
  }
  
  virtual void clear()
  {
    parsert::clear();
    parse_tree.clear();
  }
  
  verilog_parsert():mode(VIS_VERILOG)
  {
    dummy_id=0;
  }

  // parser scopes and identifiers
  struct scopet
  {
    scopet() : parent(nullptr), prefix("Verilog::")
    {
    }
    explicit scopet(
      irep_idt name,
      const std::string &separator,
      scopet *_parent)
      : parent(_parent),
        prefix(id2string(_parent->prefix) + id2string(name) + separator)
    {
    }
    scopet *parent = nullptr;
    bool is_type = false;
    using scope_mapt = std::map<irep_idt, scopet>;
    scope_mapt scope_map;
    std::string prefix;
  };

  scopet top_scope, *current_scope = &top_scope;

  scopet &add_name(irep_idt name, const std::string &separator)
  {
    auto result = current_scope->scope_map.emplace(
      name, scopet{name, separator, current_scope});
    return result.first->second;
  }

  // Create the given sub-scope of the current scope.
  void push_scope(irep_idt name, const std::string &separator)
  {
    current_scope = &add_name(name, separator);
  }

  void pop_scope()
  {
    PRECONDITION(current_scope->parent != nullptr);
    current_scope = current_scope->parent;
  }

  // Look up an identifier, starting from the current scope,
  // going upwards until found. Returns nullptr when not found.
  const scopet *lookup(irep_idt) const;

  bool is_type(irep_idt name) const
  {
    auto scope_ptr = lookup(name);
    return scope_ptr == nullptr ? false : scope_ptr->is_type;
  }

  unsigned dummy_id;

  std::string get_dummy_id()
  {
    dummy_id++;
    return integer2string(dummy_id-1);
  }
};

extern verilog_parsert verilog_parser;

bool parse_verilog_file(const std::string &filename);
void verilog_scanner_init();

#endif
