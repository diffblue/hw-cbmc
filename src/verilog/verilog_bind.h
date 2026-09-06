/*******************************************************************\

Module: Verilog bind Directives

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_VERILOG_BIND_H
#define CPROVER_VERILOG_VERILOG_BIND_H

#include "verilog_expr.h"

class symbol_table_baset;

/// The bind target, as a string, for error messages.
/// E.g., main.sub.s for an instance target.
std::string bind_target_as_string(const exprt &target);

/// The elaborated identifier of an instance target,
/// e.g., Verilog::$root.main.sub.s
irep_idt bind_target_instance_identifier(const exprt &target);

/// Registers the given bind directive, IEEE 1800-2017 23.11, in the
/// symbol table, to be applied when the target is elaborated.
/// Registering the same directive again, e.g., when the design element
/// containing the directive is elaborated a second time, has no effect.
/// Reports an error if the directive binds a module to itself, or if
/// the target has already been elaborated.
void register_bind_directive(
  const verilog_bind_directivet &,
  symbol_table_baset &);

/// Applies the registered bind directives that match the given design
/// element instance by adding the instantiation given in the directive
/// to the items of the given module source, as if it was written there.
/// Also records the elaboration of the design element, for detecting
/// bind directives that are registered too late.
void apply_bind_directives(
  verilog_module_sourcet &,
  const irep_idt &module_base_name,
  const irep_idt &instance_identifier,
  symbol_table_baset &);

/// After elaboration, checks that the targets of the registered bind
/// directives exist, and hence, that the directives have been applied.
void check_bind_directives(const symbol_table_baset &);

#endif // CPROVER_VERILOG_VERILOG_BIND_H
