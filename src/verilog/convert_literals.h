/*******************************************************************\

Module: Conversion for Verilog Literals

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_CONVERT_LITERALS_H
#define CPROVER_VERILOG_CONVERT_LITERALS_H

#include <util/std_expr.h>

#include <optional>

constant_exprt convert_string_literal(const irep_idt &);
constant_exprt convert_real_literal(const irep_idt &);
exprt convert_integral_literal(const irep_idt &);

/// \return the size given explicitly in an integral literal (as in 4'h2),
/// or an empty optional for an unsized literal
std::optional<std::size_t> integral_literal_size(const irep_idt &);

#endif
