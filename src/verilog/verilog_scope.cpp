/*******************************************************************\

Module: Verilog Scope

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_scope.h"

const verilog_scopet *verilog_scopest::lookup(irep_idt name) const
{
  // we start from the current scope, and walk upwards to the root
  auto scope = current_scope;
  while(scope != nullptr)
  {
    auto name_it = scope->scope_map.find(name);
    if(name_it == scope->scope_map.end())
      scope = scope->parent;
    else
      return &name_it->second; // found it
  }

  // not found, give up
  return nullptr;
}
