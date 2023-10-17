/*******************************************************************\

Module: Random Trace Generation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef EBMC_RANDOM_TRACES_H
#define EBMC_RANDOM_TRACES_H

#include <string>

class cmdlinet;
class message_handlert;

int random_traces(const cmdlinet &, message_handlert &);

class transition_systemt;

void random_traces(
  const transition_systemt &,
  const std::string &outfile_prefix,
  std::size_t number_of_traces,
  std::size_t number_of_trace_steps,
  message_handlert &);

#endif
