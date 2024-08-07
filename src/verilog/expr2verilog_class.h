/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_EXPR2VERILOG_H
#define CPROVER_VERILOG_EXPR2VERILOG_H

#include <util/bitvector_expr.h>
#include <util/std_expr.h>

class sva_abort_exprt;
class sva_case_exprt;
class sva_if_exprt;
class sva_ranged_predicate_exprt;

// Precedences (higher means binds more strongly).
// Follows Table 11-2 in IEEE 1800-2017.
//
enum class verilog_precedencet
{
  MAX = 19,
  MEMBER = 18,     //  [ ]  bit-select  ( )  parenthesis  ::   .
  NOT = 17,        //  unary !  ~  &  |  ~&  ~|  ^  ~^  ^~  +  -
  POWER = 16,      //  **  power
  MULT = 15,       //  *  /  %
  ADD = 14,        //  + -
  SHIFT = 13,      //  <<  >>  <<<  >>>
  RELATION = 12,   //  >  >=  <  <=
  EQUALITY = 11,   //  ==  !=  ===  !==  ==?  !=?
  BITAND = 10,     //  &
  XOR = 9,         //  ^  ~^  ^~ (binary)
  BITOR = 8,       //  |
  AND = 7,         //  &&
  OR = 6,          //  ||
  IF = 5,          //  ?:
  IMPLIES = 4,     //  ->
  ASSIGN = 3,      //  = += -= etc.
  CONCAT = 2,      //  { } concatenation
  REPLICATION = 1, //  {{ }} replication
  MIN = 0          //  anything even weaker, e.g., SVA
};

class expr2verilogt
{
public:
  explicit expr2verilogt(const namespacet &__ns) : ns(__ns)
  {
  }

  virtual ~expr2verilogt()
  {
  }

  virtual std::string convert(const typet &type);

  virtual std::string convert_array(const exprt &src, verilog_precedencet);

  virtual std::string convert_binary(
    const multi_ary_exprt &,
    const std::string &symbol,
    verilog_precedencet);

  virtual std::string convert_unary(
    const unary_exprt &,
    const std::string &symbol,
    verilog_precedencet);

  virtual std::string convert_if(const if_exprt &, verilog_precedencet);

  virtual std::string convert_index(const index_exprt &, verilog_precedencet);

  virtual std::string
  convert_extractbit(const extractbit_exprt &, verilog_precedencet);

  virtual std::string convert_member(const member_exprt &, verilog_precedencet);

  virtual std::string
  convert_extractbits(const extractbits_exprt &, verilog_precedencet);

  virtual std::string convert(const exprt &src, verilog_precedencet &);

  virtual std::string convert(const exprt &src);

  virtual std::string convert_symbol(const exprt &src, verilog_precedencet &);

  std::string convert_hierarchical_identifier(
    const class hierarchical_identifier_exprt &,
    verilog_precedencet &precedence);

  virtual std::string
  convert_nondet_symbol(const exprt &src, verilog_precedencet &);

  virtual std::string
  convert_next_symbol(const exprt &src, verilog_precedencet &);

  virtual std::string
  convert_constant(const constant_exprt &, verilog_precedencet &);

  virtual std::string
  convert_typecast(const typecast_exprt &, verilog_precedencet &);

  virtual std::string
  convert_concatenation(const concatenation_exprt &, verilog_precedencet);

  virtual std::string convert_function(
    const std::string &name,
    const exprt &src);

  std::string convert_sva_case(const sva_case_exprt &);

  std::string convert_sva_ranged_predicate(
    const std::string &name,
    const sva_ranged_predicate_exprt &);

  std::string convert_sva_unary(const std::string &name, const unary_exprt &);

  std::string convert_sva_binary(const std::string &name, const binary_exprt &);

  std::string
  convert_sva_abort(const std::string &name, const sva_abort_exprt &);

  std::string
  convert_sva_indexed_binary(const std::string &name, const binary_exprt &);

  virtual std::string
  convert_replication(const replication_exprt &, verilog_precedencet);

  virtual std::string convert_norep(const exprt &src, verilog_precedencet &);

  virtual std::string convert_with(const with_exprt &, verilog_precedencet);

  virtual std::string
  convert_sva_cycle_delay(const ternary_exprt &, verilog_precedencet);

  std::string convert_sva_if(const sva_if_exprt &);

  virtual std::string
  convert_sva_sequence_concatenation(const binary_exprt &, verilog_precedencet);

  virtual std::string convert_function_call(const class function_call_exprt &);

  std::string convert_non_indexed_part_select(
    const class verilog_non_indexed_part_select_exprt &,
    verilog_precedencet precedence);

  std::string convert_indexed_part_select(
    const class verilog_indexed_part_select_plus_or_minus_exprt &,
    verilog_precedencet precedence);

protected:
  const namespacet &ns;
};

#endif
