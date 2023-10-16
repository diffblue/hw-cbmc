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
#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>
#include <trans-word-level/instantiate_word_level.h>
#include <trans-word-level/property.h>
#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/unwind.h>

#include "ebmc_base.h"
#include "ebmc_error.h"

/*******************************************************************\

   Class: ranking_function_checkt

 Purpose:

\*******************************************************************/

class ranking_function_checkt : public ebmc_baset
{
public:
  ranking_function_checkt(
    const cmdlinet &_cmdline,
    ui_message_handlert &_ui_message_handler)
    : ebmc_baset(_cmdline, _ui_message_handler),
      ns{transition_system.symbol_table}
  {
  }

  int operator()();

protected:
  namespacet ns;

  exprt parse_ranking_function();
  propertyt &find_property();
};

int do_ranking_function(
  const cmdlinet &cmdline,
  ui_message_handlert &ui_message_handler)
{
  return ranking_function_checkt(cmdline, ui_message_handler)();
}

exprt ranking_function_checkt::parse_ranking_function()
{
  auto language = get_language_from_mode(transition_system.main_symbol->mode);
  exprt expr;

  language->set_message_handler(message.get_message_handler());

  if(language->to_expr(
       cmdline.get_value("ranking-function"),
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
  message.debug() << "Ranking function: " << expr_as_string << messaget::eom;
  message.debug() << "Mode: " << transition_system.main_symbol->mode
                  << messaget::eom;

  return expr;
}

ebmc_baset::propertyt &ranking_function_checkt::find_property()
{
  std::size_t count = 0;
  for(auto &p : properties)
  {
    if(!p.is_disabled())
      count++;
  }

  if(count == 0)
    throw ebmc_errort() << "no property given";

  if(count >= 2)
    throw ebmc_errort() << "multiple properties are given -- please pick one";

  for(auto &p : properties)
  {
    if(!p.is_disabled())
      return p;
  }

  UNREACHABLE;
}

int ranking_function_checkt::operator()()
{
  // get the transition system
  int exit_code = get_transition_system(
    cmdline, message.get_message_handler(), transition_system);

  if(exit_code != -1)
    throw ebmc_errort();

  CHECK_RETURN(transition_system.trans_expr.has_value());

  // parse the ranking function
  const auto ranking_function = parse_ranking_function();

  // find the property
  exit_code = get_properties();

  if(exit_code != -1)
    return exit_code;

  auto &property = find_property();

  satcheckt satcheck{message.get_message_handler()};
  boolbvt solver(ns, satcheck, message.get_message_handler());

  // *no* initial state, two time frames
  unwind(
    *transition_system.trans_expr,
    message.get_message_handler(),
    solver,
    2,
    ns,
    false);

  const auto p = [&property]() -> exprt
  {
    if(property.expr.id() == ID_AF)
    {
      return to_unary_expr(property.expr).op();
    }
    else if(
      property.expr.id() == ID_sva_always &&
      to_unary_expr(property.expr).op().id() == ID_sva_eventually)
    {
      return to_unary_expr(to_unary_expr(property.expr).op()).op();
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

  decision_proceduret::resultt dec_result = solver.dec_solve();

  switch(dec_result)
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
    message.result() << "SAT: inductive proof failed, check is inconclusive"
                     << messaget::eom;
    property.make_unknown();
    break;

  case decision_proceduret::resultt::D_UNSATISFIABLE:
    message.result() << "UNSAT: inductive proof successful, property holds"
                     << messaget::eom;
    property.make_success();
    break;

  case decision_proceduret::resultt::D_ERROR:
    throw ebmc_errort() << "Error from decision procedure";

  default:
    throw ebmc_errort() << "Unexpected result from decision procedure";
  }

  report_results();

  return property_failure() ? 10 : 0;
}
