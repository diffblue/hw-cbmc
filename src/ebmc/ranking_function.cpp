/*******************************************************************\

Module: Ranking Function Check

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Ranking Function Check

#include "ranking_function.h"

#include <util/std_expr.h>

#include <langapi/language.h>
#include <langapi/mode.h>
#include <trans-word-level/instantiate_word_level.h>
#include <trans-word-level/property.h>
#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/unwind.h>

#include "ebmc_base.h"
#include "ebmc_error.h"
#include "ebmc_solver_factory.h"
#include "report_results.h"

exprt parse_ranking_function(
  const std::string &string_to_be_parsed,
  const transition_systemt &transition_system,
  message_handlert &message_handler)
{
  auto language = get_language_from_mode(transition_system.main_symbol->mode);
  exprt expr;

  language->set_message_handler(message_handler);

  const namespacet ns{transition_system.symbol_table};

  if(language->to_expr(
       string_to_be_parsed,
       id2string(transition_system.main_symbol->module),
       expr,
       ns))
  {
    throw ebmc_errort() << "failed to parse ranking function";
  }

  // needs to have some numerical type
  if(expr.type().id() != ID_signedbv && expr.type().id() != ID_unsignedbv)
    throw ebmc_errort() << "ranking function must have integral bitvector type";

  std::string expr_as_string;
  language->from_expr(expr, expr_as_string, ns);
  messaget message(message_handler);
  message.debug() << "Ranking function: " << expr_as_string << messaget::eom;
  message.debug() << "Mode: " << transition_system.main_symbol->mode
                  << messaget::eom;

  return expr;
}

ebmc_propertiest::propertyt &find_property(ebmc_propertiest &properties)
{
  std::size_t count = 0;
  for(auto &p : properties.properties)
  {
    if(!p.is_disabled())
      count++;
  }

  if(count == 0)
    throw ebmc_errort() << "no property given";

  if(count >= 2)
    throw ebmc_errort() << "multiple properties are given -- please pick one";

  for(auto &p : properties.properties)
  {
    if(!p.is_disabled())
      return p;
  }

  UNREACHABLE;
}

int do_ranking_function(
  const cmdlinet &cmdline,
  message_handlert &message_handler)
{
  // get the transition system
  transition_systemt transition_system;

  int exit_code =
    get_transition_system(cmdline, message_handler, transition_system);

  if(exit_code != -1)
    throw ebmc_errort();

  CHECK_RETURN(transition_system.trans_expr.has_value());

  // parse the ranking function
  if(!cmdline.isset("ranking-function"))
    throw ebmc_errort() << "no candidate ranking function given";

  const auto ranking_function = parse_ranking_function(
    cmdline.get_value("ranking-function"), transition_system, message_handler);

  // find the property
  auto properties = ebmc_propertiest::from_transition_system(
    transition_system, message_handler);

  auto &property = find_property(properties);

  auto solver_factory = ebmc_solver_factory(cmdline);

  auto result = is_ranking_function(
    transition_system,
    property.expr,
    ranking_function,
    solver_factory,
    message_handler);

  if(result.is_true())
  {
    property.make_success();
  }
  else
  {
    property.make_unknown();
  }

  const namespacet ns(transition_system.symbol_table);
  report_results(cmdline, properties, ns, message_handler);

  return properties.property_failure() ? 10 : 0;
}

tvt is_ranking_function(
  const transition_systemt &transition_system,
  const exprt &property,
  const exprt &ranking_function,
  const ebmc_solver_factoryt &solver_factory,
  message_handlert &message_handler)
{
  const namespacet ns{transition_system.symbol_table};
  auto solver_wrapper = solver_factory(ns, message_handler);
  auto &solver = solver_wrapper.stack_decision_procedure();

  // *no* initial state, two time frames
  unwind(*transition_system.trans_expr, message_handler, solver, 2, ns, false);

  const auto p = [&property]() -> exprt
  {
    if(property.id() == ID_AF)
    {
      return to_unary_expr(property).op();
    }
    else if(
      property.id() == ID_sva_always &&
      to_unary_expr(property).op().id() == ID_sva_eventually)
    {
      return to_unary_expr(to_unary_expr(property).op()).op();
    }
    else
    {
      throw ebmc_errort()
        << "unsupported property - only SVA eventually or AF implemented";
    }
  }();

  // AF p holds if
  // a) either the ranking function decreases from timeframe 0 to 1, or
  // b) p holds in timeframe 0 or
  // c) p holds in timeframe 1

  exprt ranking_function_decreases = less_than_exprt(
    instantiate(ranking_function, 1, 2, ns),
    instantiate(ranking_function, 0, 2, ns));
  solver.set_to_false(ranking_function_decreases);

  exprt p_at_0 = instantiate(p, 0, 2, ns);
  solver.set_to_false(p_at_0);

  exprt p_at_1 = instantiate(p, 1, 2, ns);
  solver.set_to_false(p_at_1);

  decision_proceduret::resultt dec_result = solver();

  messaget message(message_handler);

  switch(dec_result)
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
    message.result()
      << "SAT: inductive proof failed, ranking function check is inconclusive"
      << messaget::eom;
    return tvt::unknown();

  case decision_proceduret::resultt::D_UNSATISFIABLE:
    message.result()
      << "UNSAT: inductive proof successful, function is a ranking function"
      << messaget::eom;
    return tvt(true);

  case decision_proceduret::resultt::D_ERROR:
    throw ebmc_errort() << "Error from decision procedure";

  default:
    throw ebmc_errort() << "Unexpected result from decision procedure";
  }
}
