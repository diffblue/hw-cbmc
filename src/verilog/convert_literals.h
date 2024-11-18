/*******************************************************************\

Module: Conversion for Verilog Literals

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_CONVERT_LITERALS_H
#define CPROVER_VERILOG_CONVERT_LITERALS_H

#include <util/std_expr.h>

constant_exprt convert_string_literal(const irep_idt &);
constant_exprt convert_real_literal(const irep_idt &);
constant_exprt convert_integral_literal(const irep_idt &);

#endif
