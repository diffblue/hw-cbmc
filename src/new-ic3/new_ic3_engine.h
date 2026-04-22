/*******************************************************************\

Module: New IC3 Engine

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Word-level IC3/PDR engine using CBMC's decision procedures.
/// Uses unwind() to encode the transition relation, with push/pop
/// for incremental SAT queries. Inspired by rIC3 (arXiv:2502.13605).

#ifndef CPROVER_NEW_IC3_NEW_IC3_ENGINE_H
#define CPROVER_NEW_IC3_NEW_IC3_ENGINE_H

#include <ebmc/property_checker.h>

property_checker_resultt new_ic3_engine(
  const cmdlinet &,
  transition_systemt &,
  ebmc_propertiest &,
  message_handlert &);

#endif // CPROVER_NEW_IC3_NEW_IC3_ENGINE_H
