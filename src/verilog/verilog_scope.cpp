/*******************************************************************\

Module: Verilog Scope

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_scope.h"

#include "verilog_y.tab.h"

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

void verilog_scopest::enter_package_scope(irep_idt base_name)
{
  // look in the global scope
  auto name_it = top_scope.scope_map.find(base_name);
  if(name_it == top_scope.scope_map.end())
    enter_scope(current_scope());
  else
    enter_scope(name_it->second); // found it
}
