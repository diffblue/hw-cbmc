/*******************************************************************\

Module: aval/bval encoding

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_AVAL_BVAL_H
#define CPROVER_VERILOG_AVAL_BVAL_H

#include <util/bitvector_types.h>
#include <util/std_expr.h>

// bit-concoding for four-valued types
//
// bval aval | 4-state Verilog value
// ----------|----------------------
//   0    0  |   0
//   0    1  |   1
//   1    0  |   X
//   1    1  |   Z

bool is_aval_bval(const typet &);
std::size_t aval_bval_width(const typet &);
typet aval_bval_underlying(const typet &);

bv_typet lower_to_aval_bval(const typet &);
constant_exprt lower_to_aval_bval(const constant_exprt &);

// extract a/b vectors
exprt aval(const exprt &);
exprt bval(const exprt &);

exprt aval_bval_conversion(const exprt &, const typet &);

std::string decode_aval_bval(const constant_exprt &);

#endif
