/*******************************************************************\

Module: Property Instrumentation via Buechi Automata

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "ltl_to_buechi.h"

#include <util/arith_tools.h>
#include <util/format_expr.h>
#include <util/message.h>
#include <util/run.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <ebmc/ebmc_error.h>
#include <trans-word-level/next_symbol.h>

#include "hoa.h"
#include "ltl_sva_to_string.h"

#include <sstream>

buechi_transt ltl_to_buechi(
  const exprt &property,
  const std::string &identifier_prefix,
  message_handlert &message_handler)
{
  buechi_transt buechi_trans;

  // Turn the skeleton of the property into a string
  auto string = ltl_sva_to_stringt{}(property);

  // Run Spot's ltl2tgba
  std::ostringstream hoa_stream;

  messaget message(message_handler);

  // state-based Buchi acceptance
  auto run_result = run(
    "ltl2tgba",
    {"ltl2tgba", "--sba", "--hoaf=1.1", string.s},
    "",
    hoa_stream,
    "");

  if(run_result != 0)
    throw ebmc_errort{} << "failed to run ltl2tgba";

  auto hoa = hoat::from_string(hoa_stream.str());

  message.debug() << hoa << messaget::eom;

  auto max_state_number = hoa.max_state_number();
  auto state_type = range_typet{0, max_state_number};
  const auto buechi_state =
    symbol_exprt{identifier_prefix + "state", state_type};
  const auto buechi_next_state =
    next_symbol_exprt{identifier_prefix + "state", state_type};

  // construct the initial state constraint
  std::vector<exprt> init_disjuncts;

  for(auto &item : hoa.header)
    if(item.first == "Start:")
    {
      if(item.second.size() != 1)
        throw ebmc_errort() << "Start header must have one token";
      auto state_number = string2integer(item.second.front());
      init_disjuncts.push_back(
        equal_exprt{buechi_state, from_integer(state_number, state_type)});
    }

  buechi_trans.init = disjunction(init_disjuncts);

  message.debug() << "Buechi initial state: " << format(buechi_trans.init)
                  << messaget::eom;

  // construct the liveness signal
  std::vector<exprt> liveness_disjuncts;

  for(auto &state : hoa.body)
    if(!state.first.acc_sig.empty())
    {
      liveness_disjuncts.push_back(equal_exprt{
        buechi_state, from_integer(state.first.number, state_type)});
    }

  buechi_trans.liveness_signal = disjunction(liveness_disjuncts);

  message.debug() << "Buechi liveness signal: "
                  << format(buechi_trans.liveness_signal) << messaget::eom;

  // construct the transition relation
  std::vector<exprt> trans_disjuncts;

  for(auto &state : hoa.body)
  {
    auto pre =
      equal_exprt{buechi_state, from_integer(state.first.number, state_type)};
    for(auto &edge : state.second)
    {
      if(edge.dest_states.size() != 1)
        throw ebmc_errort() << "edge must have one destination state";
      auto post = equal_exprt{
        buechi_next_state, from_integer(edge.dest_states.front(), state_type)};
      trans_disjuncts.push_back(and_exprt{pre, post});
    }
  }

  buechi_trans.trans = disjunction(trans_disjuncts);

  message.debug() << "Buechi transition constraint: "
                  << format(buechi_trans.trans) << messaget::eom;

  return buechi_trans;
}
