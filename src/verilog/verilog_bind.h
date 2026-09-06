/*******************************************************************\

Module: Verilog bind Directives

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_VERILOG_BIND_H
#define CPROVER_VERILOG_VERILOG_BIND_H

#include "verilog_expr.h"
#include "verilog_parse_tree.h"

#include <list>
#include <vector>

class symbol_table_baset;

/// Collects the bind directives, IEEE 1800-2017 23.11, found in the
/// given parse trees, and removes them from the parse trees.
/// Bind directives may occur at the top level or as a module item.
std::vector<verilog_bind_directivet>
collect_bind_directives(std::list<verilog_parse_treet> &);

/// Stores the given bind directives in the symbol table, for use
/// during elaboration. Reports an error if the target of a bind
/// directive with a module target does not exist, or if a bind
/// directive binds a module to itself.
void add_bind_directives(
  const std::vector<verilog_bind_directivet> &,
  symbol_table_baset &);

/// Applies the bind directives that match the given design element
/// instance by adding the instantiation given in the directive to the
/// items of the given module source, as if it was written there.
void apply_bind_directives(
  verilog_module_sourcet &,
  const irep_idt &module_base_name,
  const irep_idt &instance_identifier,
  const symbol_table_baset &);

/// After elaboration, checks that the target instances of the bind
/// directives with an instance target exist, and hence, that these
/// directives have been applied.
void check_bind_directives(const symbol_table_baset &);

#endif // CPROVER_VERILOG_VERILOG_BIND_H
