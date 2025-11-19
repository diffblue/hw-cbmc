/*******************************************************************\

Module: Random Trace Generation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef EBMC_RANDOM_TRACES_H
#define EBMC_RANDOM_TRACES_H

#include "ebmc_solver_factory.h"

#include <functional>
#include <string>

class cmdlinet;
class message_handlert;
class transition_systemt;

// many traces
int random_traces(
  const transition_systemt &,
  const cmdlinet &,
  message_handlert &);

// just one trace
int random_trace(
  const transition_systemt &,
  const cmdlinet &,
  message_handlert &);

class trans_tracet;

// many traces, VCD
void random_traces(
  const transition_systemt &,
  const std::string &outfile_prefix,
  std::size_t number_of_traces,
  std::size_t number_of_trace_steps,
  const ebmc_solver_factoryt &,
  message_handlert &);

// many traces, given to a callback
void random_traces(
  const transition_systemt &,
  std::function<void(trans_tracet)> consumer,
  std::size_t number_of_traces,
  std::size_t number_of_trace_steps,
  const ebmc_solver_factoryt &,
  message_handlert &);

#endif
