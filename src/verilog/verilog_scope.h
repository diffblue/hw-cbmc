/*******************************************************************\

Module: Verilog Scopes

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_SCOPE_H
#define CPROVER_VERILOG_SCOPE_H

#include <util/irep.h>

#include <map>

// parser scopes and identifiers
struct verilog_scopet
{
  verilog_scopet() : parent(nullptr), prefix("Verilog::")
  {
  }

  verilog_scopet(
    irep_idt _base_name,
    const std::string &separator,
    verilog_scopet *_parent)
    : parent(_parent),
      __base_name(_base_name),
      prefix(id2string(_parent->prefix) + id2string(_base_name) + separator)
  {
  }

  verilog_scopet *parent = nullptr;
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
  using scope_mapt = std::map<irep_idt, verilog_scopet>;
  scope_mapt scope_map;
};

class verilog_scopest
{
public:
  using scopet = verilog_scopet;

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
};

#endif
