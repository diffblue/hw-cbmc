/*******************************************************************\

Module: Verilog Scope

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_scope.h"

#include "verilog_y.tab.h"

#include <ostream>

const verilog_scopet *verilog_scopest::lookup(irep_idt base_name) const
{
  // we start from the current scope, and walk upwards to the root
  auto scope = &current_scope();
  while(scope != nullptr)
  {
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

    // go up
    scope = scope->parent;
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
    auto &scope = add_name(base_name, "", name_it->second.kind);
    scope.import = name_it->second.identifier();
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
