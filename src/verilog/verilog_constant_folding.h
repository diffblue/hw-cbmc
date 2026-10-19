/*******************************************************************\

Module: Verilog Constant Folding

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_VERILOG_CONSTANT_FOLDING_H
#define CPROVER_VERILOG_VERILOG_CONSTANT_FOLDING_H

#include <util/expr.h>

class namespacet;

/// Constant folding for type-checked Verilog expressions, following
/// IEEE 1800-2017 11.2.1. The operands and the result are Verilog
/// constants, i.e., two-valued vectors (signedbv, unsignedbv, bool),
/// four-valued vectors (verilog_signedbv/verilog_unsignedbv, with
/// 0/1/x/z digits), and reals (verilog_real, verilog_shortreal,
/// verilog_realtime).
///
/// The sub-expressions are folded bottom-up. An expression is folded by
/// lowering it to the back-end encoding (four-valued vectors become
/// aval/bval pairs, reals become floatbv) and running the CBMC
/// simplifier on the result. If the simplifier yields a constant, the
/// back-end constant is lifted back to the Verilog type of the
/// expression; otherwise, the expression is returned with its operands
/// folded. In particular, symbols are left alone; the caller is expected
/// to substitute elaboration-time constants.
exprt verilog_constant_folding(exprt, const namespacet &);

#endif // CPROVER_VERILOG_VERILOG_CONSTANT_FOLDING_H
