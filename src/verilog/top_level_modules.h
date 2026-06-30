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
std::vector<irep_idt>
top_level_modules(const std::list<verilog_parse_treet> &, const cmdlinet &);

#endif // EBMC_VERILOG_TOP_LEVEL_MODULES_H
