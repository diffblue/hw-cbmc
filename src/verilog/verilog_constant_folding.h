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
/// constants, which are lifted back to the Verilog type of the
/// given expression:
/// * constants of four-valued type get the four-valued Verilog type,
///   with a value that is a string of 0/1/x/z digits;
/// * constants of the real types get the Verilog real type;
/// * other constants whose type is not changed by the lowering get
///   the Verilog type, which may carry attributes, e.g. of an enum.
/// Other constants remain lowered.
exprt verilog_constant_folding(exprt, const namespacet &);

#endif
