/*******************************************************************\

Module: Verilog Type Width

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_BITS_H
#define CPROVER_VERILOG_BITS_H

#include <util/expr.h>
#include <util/mp_arith.h>

/// $bits -- throws an exception if no width
mp_integer verilog_bits(const typet &);

/// $bits -- throws an exception if no width
inline mp_integer verilog_bits(const exprt &expr)
{
  return verilog_bits(expr.type());
}

/// $bits
std::optional<mp_integer> verilog_bits_opt(const typet &);

/// Like verilog_bits_opt, but also gives the width of a bv_typet.
/// verilog_bits_opt gives no width for bv_typet, as it is not a Verilog
/// type. But to_bitvector converts a packed struct, union or array into
/// a value of type bv_typet, e.g., the concatenation of the members.
std::optional<mp_integer> bitvector_bits_opt(const typet &);

#endif
