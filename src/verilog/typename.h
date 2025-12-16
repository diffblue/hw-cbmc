/*******************************************************************\

Module: $typename

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_TYPENAME_H
#define CPROVER_VERILOG_TYPENAME_H

#include <util/mp_arith.h>

class typet;

/// Verilog's $left
mp_integer verilog_left(const typet &);

/// Verilog's $right
mp_integer verilog_right(const typet &);

/// Verilog's $typename
std::string verilog_typename(const typet &);

#endif
