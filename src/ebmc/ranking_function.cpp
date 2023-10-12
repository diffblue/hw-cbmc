/*******************************************************************\

Module: Ranking Function Check

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Ranking Function Check

#include "ranking_function.h"

#include <trans-word-level/instantiate_word_level.h>
#include <trans-word-level/property.h>
#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/unwind.h>

#include <langapi/language.h>
#include <langapi/mode.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>

#include <util/std_expr.h>

#include "ebmc_base.h"

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

  optionalt<exprt> parse_ranking_function();
  propertyt &find_property();
};

int do_ranking_function(
  const cmdlinet &cmdline,
  ui_message_handlert &ui_message_handler)
{
  return ranking_function_checkt(cmdline, ui_message_handler)();
}

optionalt<exprt> ranking_function_checkt::parse_ranking_function()
{
  auto language = get_language_from_mode(transition_system.main_symbol->mode);
  exprt expr;

  language->set_message_handler(get_message_handler());

  if(language->to_expr(
       cmdline.get_value("ranking-function"),
       id2string(transition_system.main_symbol->module),
       expr,
       ns))
  {
    error() << "failed to parse ranking function" << eom;
    return {};
  }

  // needs to have some numerical type
  if(expr.type().id() != ID_signedbv && expr.type().id() != ID_unsignedbv)
  {
    error() << "ranking function must have integral bitvector type" << eom;
    return {};
  }

  std::string expr_as_string;
  language->from_expr(expr, expr_as_string, ns);
  debug() << "Ranking function: " << expr_as_string << eom;
  debug() << "Mode: " << transition_system.main_symbol->mode << eom;

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
  {
    error() << "no property given" << eom;
    throw 0;
  }

  if(count >= 2)
  {
    error() << "multiple properties are given -- please pick one" << eom;
    throw 0;
  }

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
  int exit_code = get_transition_system();

  if(exit_code != -1)
    return exit_code;

  CHECK_RETURN(transition_system.trans_expr.has_value());

  // parse the ranking function
  const auto ranking_function_opt = parse_ranking_function();

  if(!ranking_function_opt.has_value())
    return 1;

  auto &ranking_function = ranking_function_opt.value();

  // find the property
  auto &property = find_property();

  satcheckt satcheck{*message_handler};
  boolbvt solver(ns, satcheck, *message_handler);

  // *no* initial state, two time frames
  unwind(*transition_system.trans_expr, *message_handler, solver, 2, ns, false);

  const auto p = [&property]() -> optionalt<exprt>
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
      return {};
  }();

  if(!p.has_value())
  {
    error() << "unsupported property - only SVA eventually or AF implemented"
            << eom;
    return 1;
  }

  // AF p holds if
  // a) either the ranking function decreases from timeframe 0 to 1, or
  // b) p holds in timeframe 0 or
  // c) p holds in timeframe 1

  exprt ranking_function_decreases = less_than_exprt(
    instantiate(ranking_function, 1, 2, ns),
    instantiate(ranking_function, 0, 2, ns));
  solver.set_to_false(ranking_function_decreases);

  exprt p_at_0 = instantiate(*p, 0, 2, ns);
  solver.set_to_false(p_at_0);

  exprt p_at_1 = instantiate(*p, 1, 2, ns);
  solver.set_to_false(p_at_1);

  decision_proceduret::resultt dec_result = solver.dec_solve();

  switch(dec_result)
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
    result() << "SAT: inductive proof failed, check is inconclusive" << eom;
    property.make_unknown();
    break;

  case decision_proceduret::resultt::D_UNSATISFIABLE:
    result() << "UNSAT: inductive proof successful, property holds" << eom;
    property.make_success();
    break;

  case decision_proceduret::resultt::D_ERROR:
    error() << "Error from decision procedure" << eom;
    return 2;

  default:
    error() << "Unexpected result from decision procedure" << eom;
    return 1;
  }

  report_results();

  return property_failure() ? 10 : 0;
}
