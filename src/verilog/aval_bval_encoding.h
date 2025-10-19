/*******************************************************************\

Module: aval/bval encoding

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_AVAL_BVAL_H
#define CPROVER_VERILOG_AVAL_BVAL_H

#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/mathematical_expr.h>

#include "verilog_expr.h"

// bit-concoding for four-valued types
//
// bval aval | 4-state Verilog value
// ----------|----------------------
//   0    0  |   0
//   0    1  |   1
//   1    0  |   X
//   1    1  |   Z

bool is_four_valued(const typet &);
bool is_four_valued(const exprt &);
bool is_aval_bval(const typet &);
bool is_aval_bval(const exprt &);
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

/// lowering for !
exprt aval_bval(const not_exprt &);
/// lowering for ~
exprt aval_bval(const bitnot_exprt &);
/// lowering for &, |, ^, ^~
exprt aval_bval_bitwise(const multi_ary_exprt &);
/// lowering for reduction operators
exprt aval_bval_reduction(const unary_exprt &);
/// lowering for ==?
exprt aval_bval(const verilog_wildcard_equality_exprt &);
/// lowering for !=?
exprt aval_bval(const verilog_wildcard_inequality_exprt &);
/// lowering for **
exprt aval_bval(const power_exprt &);
/// lowering for <->
exprt aval_bval(const verilog_iff_exprt &);
/// lowering for ->
exprt aval_bval(const verilog_implies_exprt &);
/// lowering for typecasts
exprt aval_bval(const typecast_exprt &);
/// lowering for shifts
exprt aval_bval(const shift_exprt &);

/// If any operand has x/z, then the result is 'x'.
/// Otherwise, the result is the expression applied to the aval
/// of the operands.
exprt default_aval_bval_lowering(const exprt &);

#endif
