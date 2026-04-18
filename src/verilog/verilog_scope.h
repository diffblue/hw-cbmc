/*******************************************************************\

Module: Verilog Scopes

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_SCOPE_H
#define CPROVER_VERILOG_SCOPE_H

#include <util/irep.h>

#include <iosfwd>
#include <map>

// parser scopes and identifiers
struct verilog_scopet
{
  using kindt = enum {
    GLOBAL,
    FILE,
    PACKAGE,
    MODULE,
    PROGRAM,
    CLASS,
    ENUM_NAME,
    MODULE_INSTANCE,
    TASK,
    FUNCTION,
    BLOCK,
    TYPEDEF,
    PARAMETER,
    PROPERTY,
    SEQUENCE,
    VAR,
    OTHER
  };

  verilog_scopet() : parent{nullptr}, prefix{}, kind{GLOBAL}
  {
  }

  verilog_scopet(
    irep_idt _base_name,
    const std::string &separator,
    verilog_scopet *_parent,
    kindt _kind)
    : parent(_parent),
      __base_name(_base_name),
      prefix(id2string(_parent->prefix) + id2string(_base_name) + separator),
      kind(_kind)
  {
  }

  verilog_scopet *parent = nullptr;
  irep_idt __base_name;
  std::string prefix;
  kindt kind;

  // if imported, this is the package and base name of the original
  irep_idt import;

  irep_idt identifier() const
  {
    PRECONDITION(parent != nullptr);
    return parent->prefix + id2string(__base_name);
  }

  const irep_idt &base_name() const
  {
    return __base_name;
  }

  void print(std::ostream &out) const
  {
    print_rec(0, out);
  }

  void print_rec(std::size_t indent, std::ostream &) const;

  // sub-scopes
  using scope_mapt = std::map<irep_idt, verilog_scopet>;
  scope_mapt scope_map;

  // wildcard imports, in source order
  using wildcard_importst = std::vector<const verilog_scopet *>;
  wildcard_importst wildcard_imports;

  //.the scanner token number
  unsigned identifier_token() const;
};

class verilog_scopest
{
public:
  using scopet = verilog_scopet;

  scopet top_scope;

  scopet &add_identifier(irep_idt _base_name, scopet::kindt);

  scopet &
  add_scope(irep_idt _base_name, const std::string &separator, scopet::kindt);

  // Scope stack
  std::vector<scopet *> scope_stack = {&top_scope};

  scopet &current_scope() const
  {
    // We never pop the top scope
    PRECONDITION(!scope_stack.empty());
    return *scope_stack.back();
  }

  // find the package scope with given base name, and enter it
  void enter_package_scope(irep_idt base_name);

  void enter_scope(scopet &scope)
  {
    scope_stack.push_back(&scope);
  }

  void enter_unit_scope();

  // Create the given sub-scope of the current scope, and enter it.
  void push_scope(
    irep_idt _base_name,
    const std::string &separator,
    scopet::kindt kind)
  {
    enter_scope(add_scope(_base_name, separator, kind));
  }

  void pop_scope()
  {
    // We never pop the top scope
    PRECONDITION(scope_stack.size() >= 2);
    scope_stack.pop_back();
  }

  void import(irep_idt package, irep_idt base_name);
  void wildcard_import(irep_idt package);

  // Look up an identifier, starting from the current scope,
  // going upwards until found. Returns nullptr when not found.
  const scopet *lookup(irep_idt base_name) const;

  // token to be returned by the scanner for the given identifier
  // in the current scope
  unsigned identifier_token(irep_idt base_name) const;
};

#endif
