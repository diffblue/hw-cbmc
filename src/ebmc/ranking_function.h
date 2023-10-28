/*******************************************************************\

Module: Ranking Function Check

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Ranking Function Check

#ifndef EBMC_RANKING_FUNCTION_H
#define EBMC_RANKING_FUNCTION_H

#include <util/threeval.h>

#include "ebmc_solver_factory.h"

class exprt;
class transition_systemt;

int do_ranking_function(const cmdlinet &, message_handlert &);

exprt parse_ranking_function(
  const std::string &,
  const transition_systemt &,
  message_handlert &);

tvt is_ranking_function(
  const transition_systemt &,
  const exprt &property,
  const exprt &ranking_function,
  const ebmc_solver_factoryt &,
  message_handlert &);

#endif // EBMC_RANKING_FUNCTION_H
