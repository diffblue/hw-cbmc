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
    if(name_it == scope->scope_map.end())
      scope = scope->parent;
    else
      return &name_it->second; // found it
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
    switch(scope->kind)
    {
    // clang-format off
    case verilog_scopet::GLOBAL:    return TOK_NON_TYPE_IDENTIFIER;
    case verilog_scopet::FILE:      return TOK_NON_TYPE_IDENTIFIER;
    case verilog_scopet::PACKAGE:   return TOK_PACKAGE_IDENTIFIER;
    case verilog_scopet::MODULE:    return TOK_NON_TYPE_IDENTIFIER;
    case verilog_scopet::CLASS:     return TOK_NON_TYPE_IDENTIFIER;
    case verilog_scopet::BLOCK:     return TOK_NON_TYPE_IDENTIFIER;
    case verilog_scopet::ENUM_NAME: return TOK_NON_TYPE_IDENTIFIER;
    case verilog_scopet::TASK:      return TOK_NON_TYPE_IDENTIFIER;
    case verilog_scopet::FUNCTION:  return TOK_NON_TYPE_IDENTIFIER;
    case verilog_scopet::TYPEDEF:   return TOK_TYPE_IDENTIFIER;
    case verilog_scopet::OTHER:     return TOK_NON_TYPE_IDENTIFIER;
      // clang-format on
    }

    UNREACHABLE;
  }
}
