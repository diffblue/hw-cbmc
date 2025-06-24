/*******************************************************************\

Module: Liveness Engine

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "liveness_engine.h"

#include <util/format_expr.h>

#include <temporal-logic/ctl.h>
#include <temporal-logic/ltl.h>
#include <verilog/sva_expr.h>

#include <deque>
#include <unordered_map>

// G F p
class is_live_exprt : public unary_predicate_exprt
{
public:
  explicit is_live_exprt(exprt op)
    : unary_predicate_exprt{"is_live", std::move(op)}
  {
  }
};

class liveness_enginet
{
public:
  liveness_enginet(
    const cmdlinet &_cmdline,
    const transition_systemt &_transition_system,
    message_handlert &_message_handler)
    : cmdline(_cmdline),
      transition_system(_transition_system),
      message(_message_handler)
  {
  }

  void operator()(const is_live_exprt &);

protected:
  const cmdlinet &cmdline;
  const transition_systemt &transition_system;
  messaget message;

  std::unordered_map<is_live_exprt, bool, irep_hash> truth;

  std::deque<std::pair<is_live_exprt, bool>> queue;

  void enqueue(const is_live_exprt &expr, bool value)
  {
    message.status() << (value ? "T: " : "F: ");
    message.status() << format(expr) << messaget::eom;
    queue.emplace_back(expr, value);
  }

  static is_live_exprt negate_p(const is_live_exprt &expr)
  {
    if(expr.op().id() == ID_not)
      return is_live_exprt{to_not_expr(expr.op()).op()};
    else if(expr.op().is_false())
      return is_live_exprt{true_exprt{}};
    else if(expr.op().is_true())
      return is_live_exprt{false_exprt{}};
    else
      return is_live_exprt{not_exprt{expr.op()}};
  }
};

void liveness_enginet::operator()(const is_live_exprt &expr)
{
  enqueue(expr, false);

  while(!queue.empty())
  {
    auto entry = queue.front();
    queue.pop_front();

    auto truth_it = truth.find(entry.first);
    if(truth_it != truth.end())
    {
      if(truth_it->second != entry.second)
      {
        message.result() << "Contradiction on " << format(expr)
                         << messaget::eom;
        return;
      }
    }
    else
    {
      // ¬GFp ⇒ GF¬p
      if(!entry.second)
        enqueue(negate_p(entry.first), true);
    }
  }
}

std::optional<is_live_exprt> is_live_expr(const exprt &expr)
{
  // G F p
  if(
    expr.id() == ID_G && to_G_expr(expr).op().id() == ID_F &&
    !has_temporal_operator(to_F_expr(to_G_expr(expr).op()).op()))
  {
    auto p = to_F_expr(to_G_expr(expr).op()).op();
    return is_live_exprt{p};
  }

  // AG AF p
  if(
    expr.id() == ID_AG && to_AG_expr(expr).op().id() == ID_AF &&
    !has_temporal_operator(to_AF_expr(to_AG_expr(expr).op()).op()))
  {
    auto p = to_AF_expr(to_AG_expr(expr).op()).op();
    return is_live_exprt{p};
  }

  // always s_eventually p
  if(
    expr.id() == ID_sva_always &&
    to_sva_always_expr(expr).op().id() == ID_sva_s_eventually &&
    !has_temporal_operator(
      to_sva_s_eventually_expr(to_sva_always_expr(expr).op()).op()))
  {
    // always s_eventually p --> AG AF p
    auto p = to_sva_s_eventually_expr(to_sva_always_expr(expr).op()).op();
    return is_live_exprt{p};
  }

  return {};
}

property_checker_resultt liveness_engine(
  const cmdlinet &cmdline,
  transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  for(auto &property : properties.properties)
  {
    auto is_live_opt = is_live_expr(property.normalized_expr);
    if(is_live_opt.has_value())
    {
      liveness_enginet{cmdline, transition_system, message_handler}(
        *is_live_opt);
    }
  }

  return property_checker_resultt{properties};
}
