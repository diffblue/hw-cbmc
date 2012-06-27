/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VHDL_EXPR2VHDL_H
#define CPROVER_VHDL_EXPR2VHDL_H

#include <expr.h>

class expr2vhdlt
{
public:
  virtual ~expr2vhdlt()
  {
  }

  virtual std::string convert(const typet &type);

  virtual std::string convert_array(
    const exprt &src,
    unsigned precedence);

  virtual std::string convert_binary(
    const exprt &src,
    const std::string &symbol,
    unsigned precedence);

  virtual std::string convert_unary(
    const exprt &src,
    const std::string &symbol,
    unsigned precedence);

  virtual std::string convert_trinary(
    const exprt &src,
    const std::string &symbol1,
    const std::string &symbol2,
    unsigned precedence);

  virtual std::string convert_index(
    const exprt &src,
    unsigned precedence);

  virtual std::string convert_extractbit(
    const exprt &src,
    unsigned precedence);

  virtual std::string convert_member(
    const exprt &src,
    unsigned precedence);

  virtual std::string convert_extractbits(
    const exprt &src,
    unsigned precedence);

  virtual std::string convert(
    const exprt &src,
    unsigned &precedence);

  virtual std::string convert(const exprt &src);

  virtual std::string convert_symbol(
    const exprt &src,
    unsigned &precedence);

  virtual std::string convert_nondet_symbol(
    const exprt &src,
    unsigned &precedence);

  virtual std::string convert_next_symbol(
    const exprt &src,
    unsigned &precedence);

  virtual std::string convert_constant(
    const exprt &src,
    unsigned &precedence);

  virtual std::string convert_typecast(
    const exprt &src,
    unsigned &precedence);

  virtual std::string convert_concatenation(
    const exprt &src,
    unsigned precedence);

  virtual std::string convert_replication(
    const exprt &src,
    unsigned precedence);

  virtual std::string convert_norep(
    const exprt &src,
    unsigned &precedence);

  virtual std::string convert_with(
    const exprt &src,
    unsigned precedence);
};

#endif
