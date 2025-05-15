/*******************************************************************\

Module: Verilog Initializer

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_INITIALIZER_H
#define CPROVER_VERILOG_INITIALIZER_H

#include <optional>

class exprt;
class typet;

std::optional<exprt> verilog_zero_initializer(const typet &);

#endif
