/*******************************************************************\

Module: Verilog Lowering

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_LOWERING_H
#define CPROVER_VERILOG_LOWERING_H

class exprt;
class typecast_exprt;
class typet;

exprt verilog_lowering(exprt);
typet verilog_lowering(typet);

exprt verilog_lowering_cast(typecast_exprt);

/// Convert an aggregate-typed (struct/union/packed-array) expression to
/// its packed bit-vector representation, following the SystemVerilog
/// packed layout (1800-2017 7.2.1: the first struct member and, for
/// packed arrays, the most significant index occupy the most-significant
/// bits). Non-aggregate expressions are returned unchanged.
exprt to_bitvector(const exprt &);

#endif
