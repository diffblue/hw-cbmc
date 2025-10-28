/*******************************************************************\

Module: Property Instrumentation via Buechi Automata

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "ltl_to_buechi.h"

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/message.h>
#include <util/replace_expr.h>
#include <util/run.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <ebmc/ebmc_error.h>
#include <trans-word-level/next_symbol.h>

#include "hoa.h"
#include "ltl_sva_to_string.h"

#include <sstream>

void buechi_transt::rename_state_symbol(const symbol_exprt &new_state_symbol)
{
  next_symbol_exprt old_next_symbol{
    state_symbol.get_identifier(), state_symbol.type()};
  next_symbol_exprt new_next_symbol{
    new_state_symbol.get_identifier(), state_symbol.type()};

  replace_mapt replace_map;
  replace_map.insert({state_symbol, new_state_symbol});
  replace_map.insert({old_next_symbol, new_next_symbol});

  replace_expr(replace_map, init);
  replace_expr(replace_map, trans);
  replace_expr(replace_map, error_signal);
  replace_expr(replace_map, liveness_signal);

  state_symbol = new_state_symbol;
}

exprt hoa_label_to_expr(
  const hoat::labelt &label,
  const ltl_sva_to_stringt &ltl_sva_to_string)
{
  std::vector<exprt> operands;
  operands.reserve(label.get_sub().size());
  for(auto &sub : label.get_sub())
    operands.push_back(hoa_label_to_expr(sub, ltl_sva_to_string));

  if(label.id() == "t")
  {
    return true_exprt{};
  }
  else if(label.id() == "f")
  {
    return false_exprt{};
  }
  else if(label.id() == "|")
  {
    PRECONDITION(operands.size() == 2);
    return or_exprt{operands};
  }
  else if(label.id() == "&")
  {
    PRECONDITION(operands.size() == 2);
    return and_exprt{operands};
  }
  else if(label.id() == "!")
  {
    PRECONDITION(operands.size() == 1);
    return not_exprt{operands[0]};
  }
  else
  {
    // atomic proposition, given as number
    return ltl_sva_to_string.atom(label.id_string());
  }
}

// a nonaccepting state with an unconditional self-loop
bool is_error_state(const std::pair<hoat::state_namet, hoat::edgest> &state)
{
  if(!state.first.is_accepting())
    return false;

  for(auto &edge : state.second)
  {
    if(edge.label.id() == "t")
      for(auto &dest : edge.dest_states)
        if(dest == state.first.number)
          return true;
  }

  return false;
}

/// Returns true iff all accepting states of the automaton have
/// unconditional self loops
bool is_safety_only(const hoat &hoa)
{
  for(auto &state : hoa.body)
    if(state.first.is_accepting() && !is_error_state(state))
      return false;

  return true;
}

buechi_transt
ltl_to_buechi(const exprt &property, message_handlert &message_handler)
{
  ltl_sva_to_stringt ltl_sva_to_string;

  try
  {
    // Turn the skeleton of the property into a string
    auto string = ltl_sva_to_string(property);

    // Run Spot's ltl2tgba
    std::ostringstream hoa_stream;

    messaget message(message_handler);

    message.debug() << "ltl2tgba property: " << string << messaget::eom;

    // State-based Buchi acceptance. Should compare with transition-based
    // acceptance.
    // Use --complete to be able to have multiple properties in one
    // model.
    auto run_result = run(
      "ltl2tgba",
      {"ltl2tgba", "--sba", "--complete", "--hoaf=1.1", string},
      "",
      hoa_stream,
      "");

    if(run_result != 0)
      throw ebmc_errort{} << "failed to run ltl2tgba";

    auto hoa = hoat::from_string(hoa_stream.str());

    message.debug() << hoa << messaget::eom;

    // clean up accepting states
    hoa.buechi_acceptance_cleanup();

    auto max_state_number = hoa.max_state_number();
    auto state_type = range_typet{0, max_state_number};
    const auto buechi_state = symbol_exprt{"buechi::state", state_type};
    const auto buechi_next_state =
      next_symbol_exprt{"buechi::state", state_type};

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

    auto init = disjunction(init_disjuncts);

    message.debug() << "Buechi initial state: " << format(init)
                    << messaget::eom;

    exprt liveness_signal;

    // Is safety sufficient?
    if(is_safety_only(hoa))
    {
      liveness_signal = false_exprt{};

      message.debug() << "Buechi liveness signal not required" << messaget::eom;
    }
    else
    {
      // construct the liveness signal
      std::vector<exprt> liveness_disjuncts;

      for(auto &state : hoa.body)
        if(state.first.is_accepting())
        {
          liveness_disjuncts.push_back(equal_exprt{
            buechi_state, from_integer(state.first.number, state_type)});
        }

      liveness_signal = disjunction(liveness_disjuncts);

      message.debug() << "Buechi liveness signal: " << format(liveness_signal)
                      << messaget::eom;
    }

    // construct the error signal -- true when the next automaton state
    // is nonaccepting with an unconditional self-loop.
    std::vector<exprt> error_disjuncts;

    std::map<hoat::intt, std::pair<hoat::state_namet, hoat::edgest>> state_map;
    for(auto &state : hoa.body)
      state_map[state.first.number] = state;

    for(auto &state : hoa.body)
    {
      for(auto &edge : state.second)
      {
        if(edge.dest_states.size() != 1)
          throw ebmc_errort() << "edge must have one destination state";
        auto dest_state_it = state_map.find(edge.dest_states.front());
        CHECK_RETURN(dest_state_it != state_map.end());
        if(is_error_state(dest_state_it->second))
        {
          auto pre = equal_exprt{
            buechi_state, from_integer(state.first.number, state_type)};
          auto cond = hoa_label_to_expr(edge.label, ltl_sva_to_string);
          error_disjuncts.push_back(and_exprt{pre, cond});
        }
      }
    }

    auto error_signal = disjunction(error_disjuncts);

    message.debug() << "Buechi error signal: " << format(error_signal)
                    << messaget::eom;

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
        auto cond = hoa_label_to_expr(edge.label, ltl_sva_to_string);
        auto post = equal_exprt{
          buechi_next_state,
          from_integer(edge.dest_states.front(), state_type)};
        trans_disjuncts.push_back(and_exprt{pre, cond, post});
      }
    }

    auto trans = disjunction(trans_disjuncts);

    message.debug() << "Buechi transition constraint: " << format(trans)
                    << messaget::eom;

    return {
      buechi_state,
      std::move(init),
      std::move(trans),
      std::move(error_signal),
      std::move(liveness_signal)};
  }
  catch(ltl_sva_to_string_unsupportedt error)
  {
    // re-throw
    throw ltl_to_buechi_unsupportedt{error.expr};
  }
}
