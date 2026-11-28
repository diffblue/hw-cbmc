/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VHDL_EXPR2VHDL_H
#define CPROVER_VHDL_EXPR2VHDL_H

#include <util/bitvector_expr.h>
#include <util/std_expr.h>

/// Prints the lowered expressions of the VHDL front-end in VHDL syntax
class expr2vhdlt
{
public:
  virtual ~expr2vhdlt()
  {
  }

  virtual std::string convert(const typet &type);
  virtual std::string convert(const exprt &src, unsigned &precedence);
  virtual std::string convert(const exprt &src);

  /// the operand, in parentheses if it binds less tightly
  virtual std::string convert_operand(const exprt &, unsigned precedence);

  virtual std::string
  convert_binary(const exprt &, const std::string &symbol, unsigned precedence);
  virtual std::string convert_logical(
    const exprt &,
    const std::string &symbol,
    unsigned &precedence);
  virtual std::string convert_unary(
    const unary_exprt &,
    const std::string &symbol,
    unsigned precedence);
  virtual std::string convert_if(const if_exprt &);

  virtual std::string convert_array(const array_exprt &, unsigned precedence);
  virtual std::string
  convert_array_of(const array_of_exprt &, unsigned precedence);
  virtual std::string convert_struct(const struct_exprt &, unsigned precedence);
  virtual std::string
  convert_concatenation(const concatenation_exprt &, unsigned precedence);
  virtual std::string
  convert_replication(const replication_exprt &, unsigned precedence);
  virtual std::string convert_with(const with_exprt &, unsigned precedence);
  virtual std::string
  convert_update_bit(const update_bit_exprt &, unsigned precedence);

  virtual std::string convert_index(const index_exprt &, unsigned precedence);
  virtual std::string
  convert_extractbit(const extractbit_exprt &, unsigned precedence);
  virtual std::string
  convert_extractbits(const extractbits_exprt &, unsigned precedence);
  virtual std::string convert_member(const member_exprt &, unsigned precedence);
  virtual std::string
  convert_typecast(const typecast_exprt &, unsigned &precedence);

  virtual std::string
  convert_symbol(const symbol_exprt &, unsigned &precedence);
  virtual std::string
  convert_nondet_symbol(const exprt &src, unsigned &precedence);
  virtual std::string
  convert_next_symbol(const exprt &src, unsigned &precedence);
  virtual std::string
  convert_constant(const constant_exprt &, unsigned &precedence);

  virtual std::string convert_norep(const exprt &src, unsigned &precedence);
};

#endif
