/*******************************************************************\

Module: Verilog Scope

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_scope.h"

#include "verilog_y.tab.h"

#include <ostream>

verilog_scopet &
verilog_scopest::add_identifier(irep_idt _base_name, scopet::kindt kind)
{
  return add_scope(_base_name, std::string{}, kind);
}

verilog_scopet &verilog_scopest::add_scope(
  irep_idt _base_name,
  const std::string &separator,
  scopet::kindt kind)
{
  auto result = current_scope().scope_map.emplace(
    _base_name, scopet{_base_name, separator, &current_scope(), kind});
  return result.first->second;
}

const verilog_scopet *verilog_scopest::lookup(irep_idt base_name) const
{
  // We start from the top of the scope stack, and walk downwards.
  // Note that this order may differ from the child-parent relationship;
  // e.g., module scopes are not contained in the $unit scope, but
  // lookup order is module -> $unit -> $root.
  for(auto scope_it = scope_stack.rbegin(); scope_it != scope_stack.rend();
      scope_it++)
  {
    const auto scope = *scope_it;

    auto name_it = scope->scope_map.find(base_name);
    if(name_it != scope->scope_map.end())
      return &name_it->second; // found it

    // Wildcard imports? Start with the most recent one.
    for(auto r_it = scope->wildcard_imports.rbegin();
        r_it != scope->wildcard_imports.rend();
        r_it++)
    {
      // find the identifier in the package
      const auto &package = **r_it;

      auto name_it = package.scope_map.find(base_name);
      if(name_it != package.scope_map.end())
      {
        auto result = scope->scope_map.emplace(
          base_name,
          verilog_scopet{base_name, "", scope, name_it->second.kind});
        CHECK_RETURN(result.second);
        auto &new_scope = result.first->second;
        new_scope.import = name_it->second.identifier();
        return &new_scope;
      }
    }
  }

  // not found, give up
  return nullptr;
}

void verilog_scopet::print_rec(std::size_t indent, std::ostream &out) const
{
  out << std::string(indent, ' ') << prefix << '\n';
  for(auto &scope_it : scope_map)
    scope_it.second.print_rec(indent + 2, out);
}

unsigned verilog_scopet::identifier_token() const
{
  switch(kind)
  {
  // clang-format off
  case verilog_scopet::GLOBAL:          return TOK_NON_TYPE_IDENTIFIER;
  case verilog_scopet::FILE:            return TOK_NON_TYPE_IDENTIFIER;
  case verilog_scopet::PACKAGE:         return TOK_PACKAGE_IDENTIFIER;
  case verilog_scopet::MODULE:          return TOK_NON_TYPE_IDENTIFIER;
  case verilog_scopet::CLASS:           return TOK_CLASS_IDENTIFIER;
  case verilog_scopet::MODULE_INSTANCE: return TOK_NON_TYPE_IDENTIFIER;
  case verilog_scopet::BLOCK:           return TOK_NON_TYPE_IDENTIFIER;
  case verilog_scopet::ENUM_NAME:       return TOK_NON_TYPE_IDENTIFIER;
  case verilog_scopet::TASK:            return TOK_NON_TYPE_IDENTIFIER;
  case verilog_scopet::FUNCTION:        return TOK_NON_TYPE_IDENTIFIER;
  case verilog_scopet::TYPEDEF:         return TOK_TYPE_IDENTIFIER;
  case verilog_scopet::PARAMETER:       return TOK_NON_TYPE_IDENTIFIER;
  case verilog_scopet::PROPERTY:        return TOK_NON_TYPE_IDENTIFIER;
  case verilog_scopet::SEQUENCE:        return TOK_NON_TYPE_IDENTIFIER;
  case verilog_scopet::VAR:             return TOK_NON_TYPE_IDENTIFIER;
  case verilog_scopet::OTHER:           return TOK_NON_TYPE_IDENTIFIER;
    // clang-format on
  }

  UNREACHABLE;
}

void verilog_scopest::import(irep_idt package, irep_idt base_name)
{
  // find the package in the global scope
  auto package_it = top_scope.scope_map.find(package);
  if(package_it == top_scope.scope_map.end())
    return;

  // find the identifier in the package
  auto name_it = package_it->second.scope_map.find(base_name);
  if(name_it != package_it->second.scope_map.end())
  {
    auto &identifier = add_identifier(base_name, name_it->second.kind);
    identifier.import = name_it->second.identifier();
  }
  else
  {
  }
}

void verilog_scopest::wildcard_import(irep_idt package)
{
  // find the package in the global scope
  auto package_it = top_scope.scope_map.find(package);
  if(package_it == top_scope.scope_map.end())
    return;

  current_scope().wildcard_imports.push_back(&package_it->second);
}

void verilog_scopest::enter_package_scope(irep_idt base_name)
{
  // look in the global scope
  auto name_it = top_scope.scope_map.find(base_name);
  if(name_it == top_scope.scope_map.end())
    enter_scope(current_scope());
  else
    enter_scope(name_it->second); // found it
}

void verilog_scopest::enter_unit_scope()
{
  enter_scope(top_scope);
}

unsigned verilog_scopest::identifier_token(irep_idt base_name) const
{
  auto scope = lookup(base_name);
  if(scope == nullptr)
  {
    return TOK_NON_TYPE_IDENTIFIER;
  }
  else
  {
    return scope->identifier_token();
  }
}
