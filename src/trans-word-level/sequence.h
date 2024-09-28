/*******************************************************************\

Module: Encoding SVA sequences

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_WORD_LEVEL_SEQUENCE_H
#define CPROVER_TRANS_WORD_LEVEL_SEQUENCE_H

#include <util/expr.h>
#include <util/mp_arith.h>

/// Returns a list of match points and matching conditions
/// for the given sequence expression starting at time t
[[nodiscard]] std::vector<std::pair<mp_integer, exprt>> instantiate_sequence(
  exprt expr,
  const mp_integer &t,
  const mp_integer &no_timeframes);

#endif // CPROVER_TRANS_WORD_LEVEL_SEQUENCE_H
