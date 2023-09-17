/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_EXPR2VERILOG_H
#define CPROVER_VERILOG_EXPR2VERILOG_H

#include <util/bitvector_expr.h>
#include <util/std_expr.h>

class expr2verilogt
{
public:
  virtual ~expr2verilogt()
  {
  }

  virtual std::string convert(const typet &type);

  virtual std::string convert_array(
    const exprt &src,
    unsigned precedence);

  virtual std::string convert_binary(
    const multi_ary_exprt &,
    const std::string &symbol,
    unsigned precedence);

  virtual std::string convert_unary(
    const unary_exprt &,
    const std::string &symbol,
    unsigned precedence);

  virtual std::string convert_if(const if_exprt &, unsigned precedence);

  virtual std::string convert_index(const index_exprt &, unsigned precedence);

  virtual std::string
  convert_extractbit(const extractbit_exprt &, unsigned precedence);

  virtual std::string convert_member(const member_exprt &, unsigned precedence);

  virtual std::string
  convert_extractbits(const extractbits_exprt &, unsigned precedence);

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

  virtual std::string
  convert_constant(const constant_exprt &, unsigned &precedence);

  virtual std::string
  convert_typecast(const typecast_exprt &, unsigned &precedence);

  virtual std::string
  convert_concatenation(const concatenation_exprt &, unsigned precedence);

  virtual std::string convert_function(
    const std::string &name,
    const exprt &src);

  virtual std::string convert_sva(
    const std::string &name,
    const exprt &src);

  virtual std::string
  convert_replication(const replication_exprt &, unsigned precedence);

  virtual std::string convert_norep(
    const exprt &src,
    unsigned &precedence);

  virtual std::string convert_with(const with_exprt &, unsigned precedence);

  virtual std::string
  convert_sva_cycle_delay(const ternary_exprt &, unsigned precedence);

  virtual std::string
  convert_sva_sequence_concatenation(const binary_exprt &, unsigned precedence);

  virtual std::string convert_function_call(const class function_call_exprt &);
};

#endif
