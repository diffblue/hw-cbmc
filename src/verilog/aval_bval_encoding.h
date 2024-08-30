/*******************************************************************\

Module: aval/bval encoding

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_AVAL_BVAL_H
#define CPROVER_VERILOG_AVAL_BVAL_H

#include <util/bitvector_types.h>

#include "verilog_expr.h"

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

exprt aval_bval_concatenation(const exprt::operandst &, const typet &);

exprt aval_bval(const verilog_logical_equality_exprt &);
exprt aval_bval(const verilog_logical_inequality_exprt &);

#endif
