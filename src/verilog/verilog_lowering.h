/*******************************************************************\

Module: Verilog Lowering

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_LOWERING_H
#define CPROVER_VERILOG_LOWERING_H

#include <util/expr_identity_map.h>

class symbol_table_baset;
class typecast_exprt;
class typet;

exprt verilog_lowering(exprt);
typet verilog_lowering(typet);

/// Lowers expressions, once per distinct expression node. The
/// expressions that are lowered by the same instance share the lowering
/// of their common subexpressions; this keeps, e.g., the definitions of
/// different variables of a transition relation that read the same
/// subexpression shared after lowering.
class verilog_loweringt
{
public:
  exprt operator()(const exprt &);

private:
  expr_identity_mapt<exprt> cache;
};

exprt verilog_lowering_cast(typecast_exprt);

/// The type checker gives the symbols in the symbol table their Verilog
/// types, e.g. a four-valued vector type for a variable declared as
/// reg [7:0], or verilog_real for a variable declared as real. The
/// back-ends read the types of symbols from the symbol table, and need the
/// lowered types, see verilog_lowering(typet). This lowers the types of
/// the variables and nets, and of the ports of the modules, once the
/// transition relation has been built.
void verilog_lower_symbol_types(symbol_table_baset &);

/// Convert an aggregate-typed (struct/union/packed-array) expression to
/// its packed bit-vector representation, following the SystemVerilog
/// packed layout (1800-2017 7.2.1: the first struct member and, for
/// packed arrays, the most significant index occupy the most-significant
/// bits). Non-aggregate expressions are returned unchanged.
exprt to_bitvector(const exprt &);

#endif
