/*******************************************************************\

Module: SMV Expression Output

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_SMV_EXPR2SMV_CLASS_H
#define CPROVER_SMV_EXPR2SMV_CLASS_H

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include "expr2smv.h"

class expr2smvt
{
public:
  explicit expr2smvt(const namespacet &__ns) : ns(__ns)
  {
  }

protected:
  // In NuSMV 2.6., ! (not)  has a high precedence (above ::), whereas
  // in the CMU SMV implementation it has the same as other boolean operators.
  // We use the CMU SMV precedence for !.
  // Like CMU SMV, we give the same precedence to -> and <->, to avoid ambiguity.
  // Note that the precedence of mod in the CMU SMV differs from NuSMV's.
  // We use NuSMV's.
  enum class precedencet
  {
    MAX = 16,
    INDEX = 15,   // [ ] , [ : ]
    CONCAT = 14,  // ::
    UMINUS = 13,  // - (unary minus)
    MULT = 12,    // * / mod
    PLUS = 11,    // + -
    SHIFT = 10,   // << >>
    UNION = 9,    // union
    IN = 8,       // in
    REL = 7,      // = != < > <= >=
    TEMPORAL = 6, // AX, AF, etc.
    NOT = 5,      // !
    AND = 4,      // &
    OR = 3,       // | xor xnor
    IF = 2,       // (• ? • : •)
    IFF = 1,      // <->
    IMPLIES = 1   // ->
  };

  /*
   From http://www.cs.cmu.edu/~modelcheck/smv/smvmanual.ps

  The order of precedence from high to low is
    * /
    + -
    mod
    = != < > <= >=
    !
    &
    |
    -> <->
  */

public:
  bool convert_nondet_choice(const exprt &src, std::string &dest, precedencet);

  bool convert_binary(
    const exprt &src,
    std::string &dest,
    const std::string &symbol,
    precedencet);

  bool convert_rtctl(
    const ternary_exprt &src,
    std::string &dest,
    const std::string &symbol,
    precedencet);

  bool convert_rtctl(
    const multi_ary_exprt &src,
    std::string &dest,
    const std::string &symbol1,
    const std::string &symbol2,
    precedencet);

  bool convert_unary(
    const unary_exprt &,
    std::string &dest,
    const std::string &symbol,
    precedencet);

  bool convert_index(const index_exprt &, std::string &dest, precedencet);

  bool convert(const exprt &src, std::string &dest, precedencet &);

  bool convert_if(const if_exprt &, std::string &dest, precedencet);

  std::string convert(const exprt &);

  bool convert(const exprt &, std::string &dest);

  bool convert_symbol(const symbol_exprt &, std::string &dest, precedencet &);

  bool convert_next_symbol(const exprt &src, std::string &dest, precedencet &);

  bool
  convert_constant(const constant_exprt &, std::string &dest, precedencet &);

  bool convert_cond(const exprt &src, std::string &dest);

  bool convert_norep(const exprt &src, std::string &dest, precedencet &);

protected:
  const namespacet &ns;
};

#endif // CPROVER_SMV_EXPR2SMV_CLASS_H
