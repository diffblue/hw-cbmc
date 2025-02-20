/*******************************************************************\

Module: Verilog Initializer

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_INITIALIZER_H
#define CPROVER_VERILOG_INITIALIZER_H

#include <optional>

class exprt;
class typet;

/// The default initial value, 1800-2017 Table 6-7
std::optional<exprt> verilog_default_initializer(const typet &);

#endif
