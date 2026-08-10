/*******************************************************************\

Module: Verilog Top Level Modules

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Verilog Top Level Modules

#ifndef EBMC_VERILOG_TOP_LEVEL_MODULES_H
#define EBMC_VERILOG_TOP_LEVEL_MODULES_H

#include "verilog_parse_tree.h"

class cmdlinet;

// Returns the base_names of the top-level modules in alphabetical order.
// Throws ebmc_errort when a given top-level module is not found,
// or when there is no top-level module.
// The library_count parameter specifies how many parse trees at the end
// of the list are library files. Modules in library parse trees are
// excluded from top-level consideration but still used for dependency
// erasure.
std::vector<irep_idt> top_level_modules(
  const std::list<verilog_parse_treet> &,
  const cmdlinet &,
  std::size_t library_count = 0);

#endif // EBMC_VERILOG_TOP_LEVEL_MODULES_H
