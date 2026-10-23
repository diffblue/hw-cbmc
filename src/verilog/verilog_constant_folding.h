/*******************************************************************\

Module: Verilog Constant Folding

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_CONSTANT_FOLDING_H
#define CPROVER_VERILOG_CONSTANT_FOLDING_H

class exprt;
class namespacet;

/// Given a Verilog expression, not lowered, recursively
/// fold subexpressions with constant operands into a constant,
/// according to IEEE 1800-2017 Section 11.2.1.
/// The expression returned is lowered, with the exception of
/// constants of four-valued type, which are lifted back to the
/// four-valued Verilog type.
exprt verilog_constant_folding(exprt, const namespacet &);

#endif
