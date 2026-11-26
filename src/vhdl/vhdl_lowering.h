/*******************************************************************\

Module: VHDL Lowering

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// VHDL Lowering
///
/// Maps the VHDL types (vhdl_types.h) to CBMC types, and the operators
/// on VHDL-typed operands to CBMC operators. This is done after
/// synthesis, on the symbol table.

#ifndef CPROVER_VHDL_VHDL_LOWERING_H
#define CPROVER_VHDL_VHDL_LOWERING_H

#include <util/expr.h>
#include <util/symbol_table_base.h>
#include <util/type.h>

/// the CBMC type for a VHDL type; CBMC types are returned unchanged
typet vhdl_lowering(const typet &);

/// the CBMC expression for a VHDL-typed expression
exprt vhdl_lowering(exprt);

/// lower the types and values of the VHDL symbols in the symbol table
void vhdl_lowering(symbol_table_baset &);

#endif // CPROVER_VHDL_VHDL_LOWERING_H
