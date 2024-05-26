/*******************************************************************\

Module: Traces to Tensors

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "batch.h"
#include "vcd_parser.h"

#include <map>
#include <vector>

struct state_variablet
{
  std::size_t index;
  std::string reference;
};

using state_variablest = std::map<std::string, state_variablet>;

using tracest = std::list<vcdt>;

std::vector<batcht> traces_to_tensors(
  const state_variablest &,
  const std::string &liveness_signal,
  const tracest &traces,
  std::size_t batch_size);
