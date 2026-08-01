/*******************************************************************\

Module: Verilog Constants

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_VERILOG_CONSTANT_H
#define CPROVER_VERILOG_VERILOG_CONSTANT_H

class exprt;

/// Returns true iff the given expression is a constant.
/// This includes $ (ID_infinity), and struct, union and array
/// expressions whose operands are all constants.
/// The expression is expected to be elaborated: references to
/// parameters must already have been replaced by their values,
/// since a symbol is never considered constant.
/// No evaluation is performed; in particular, calls to system
/// functions (such as $clog2) are not evaluated, and are hence
/// not considered constant.
bool is_verilog_constant(const exprt &);

#endif // CPROVER_VERILOG_VERILOG_CONSTANT_H
