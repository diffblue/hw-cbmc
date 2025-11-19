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
class trans_tracet;

int do_ranking_function(
  const transition_systemt &,
  const cmdlinet &,
  message_handlert &);

exprt parse_ranking_function(
  const std::string &,
  const transition_systemt &,
  message_handlert &);

std::pair<tvt, std::optional<trans_tracet>> is_ranking_function(
  const transition_systemt &,
  const exprt &property,
  const exprt &ranking_function,
  const ebmc_solver_factoryt &,
  message_handlert &);

#endif // EBMC_RANKING_FUNCTION_H
