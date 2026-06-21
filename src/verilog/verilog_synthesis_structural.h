/*******************************************************************\

Module: Verilog Synthesis (Structural)

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Structural synthesis: module instantiation, port connection,
/// and built-in gate expansion.

#ifndef CPROVER_VERILOG_SYNTHESIS_STRUCTURAL_H
#define CPROVER_VERILOG_SYNTHESIS_STRUCTURAL_H

class exprt;
class irep_idt;
class module_typet;
class source_locationt;
class symbolt;
class transt;
class verilog_instt;
class verilog_inst_builtint;

#include <util/irep.h>

#include "verilog_expr.h"

#include <vector>

/// Interface for structural synthesis methods. These are implemented
/// in verilog_synthesis_structural.cpp as methods of verilog_synthesist.
/// This header documents the logical grouping.
///
/// Structural synthesis has no private state beyond what the parent
/// class provides (symbol_table, ns, assignments, etc.).

#endif // CPROVER_VERILOG_SYNTHESIS_STRUCTURAL_H
