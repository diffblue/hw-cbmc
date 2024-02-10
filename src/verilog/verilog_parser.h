/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef VERILOG_PARSER_H
#define VERILOG_PARSER_H

#include <util/mp_arith.h>
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
  }

  // parser scopes and identifiers
  struct scopet
  {
    scopet() : parent(nullptr), prefix("Verilog::")
    {
    }

    explicit scopet(
      irep_idt _base_name,
      const std::string &separator,
      scopet *_parent)
      : parent(_parent),
        __base_name(_base_name),
        prefix(id2string(_parent->prefix) + id2string(_base_name) + separator)
    {
    }

    scopet *parent = nullptr;
    bool is_type = false;
    irep_idt __base_name;
    std::string prefix;

    irep_idt identifier() const
    {
      PRECONDITION(parent != nullptr);
      return parent->prefix + id2string(__base_name);
    }

    const irep_idt &base_name() const
    {
      return __base_name;
    }

    // sub-scopes
    using scope_mapt = std::map<irep_idt, scopet>;
    scope_mapt scope_map;
  };

  scopet top_scope, *current_scope = &top_scope;

  scopet &add_name(irep_idt _base_name, const std::string &separator)
  {
    auto result = current_scope->scope_map.emplace(
      _base_name, scopet{_base_name, separator, current_scope});
    return result.first->second;
  }

  // Create the given sub-scope of the current scope.
  void push_scope(irep_idt _base_name, const std::string &separator)
  {
    current_scope = &add_name(_base_name, separator);
  }

  void pop_scope()
  {
    PRECONDITION(current_scope->parent != nullptr);
    current_scope = current_scope->parent;
  }

  // Look up an identifier, starting from the current scope,
  // going upwards until found. Returns nullptr when not found.
  const scopet *lookup(irep_idt base_name) const;

  bool is_type(irep_idt base_name) const
  {
    auto scope_ptr = lookup(base_name);
    return scope_ptr == nullptr ? false : scope_ptr->is_type;
  }

  // These are used for anonymous gate instances
  // and to create a unique identifier for enum types.
  std::size_t next_id_counter = 0;

  std::string get_next_id()
  {
    next_id_counter++;
    return integer2string(next_id_counter - 1);
  }
};

extern verilog_parsert verilog_parser;

bool parse_verilog_file(const std::string &filename);
void verilog_scanner_init();

#endif
