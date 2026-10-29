/*******************************************************************\

Module: Verilog Lowering

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_LOWERING_H
#define CPROVER_VERILOG_LOWERING_H

class exprt;
class symbol_table_baset;
class typecast_exprt;
class typet;

exprt verilog_lowering(exprt);
typet verilog_lowering(typet);

exprt verilog_lowering_cast(typecast_exprt);

/// The type checker needs the Verilog types of the symbols in the symbol
/// table, e.g. verilog_real for a variable declared as real. The back-ends
/// read the types of symbols from the symbol table, and need the lowered
/// types. This lowers the types of the Verilog symbols that are still
/// Verilog-specific after elaboration (the real types, chandle and event)
/// once type checking is complete.
void verilog_lower_symbol_types(symbol_table_baset &);

/// Convert an aggregate-typed (struct/union/packed-array) expression to
/// its packed bit-vector representation, following the SystemVerilog
/// packed layout (1800-2017 7.2.1: the first struct member and, for
/// packed arrays, the most significant index occupy the most-significant
/// bits). Non-aggregate expressions are returned unchanged.
exprt to_bitvector(const exprt &);

#endif
