/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/expr.h>

std::string expr2verilog(const exprt &, const namespacet &);
std::string type2verilog(const typet &, const namespacet &);

std::string verilog_string_literal(const std::string &);
