/*******************************************************************\

Module: Waveform Trace Output

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "waveform.h"

#include <util/console.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <langapi/language_util.h>

#include <algorithm>
#include <map>
#include <unordered_set>

std::vector<irep_idt>
lhs_symbols(const trans_tracet &trace, const namespacet &ns)
{
  std::unordered_set<irep_idt, irep_id_hash> identifier_set;

  for(auto &state : trace.states)
    for(auto &assignment : state.assignments)
    {
      auto &lhs = assignment.lhs;
      if(lhs.id() == ID_symbol)
      {
        auto identifier = to_symbol_expr(lhs).get_identifier();
        auto &symbol = ns.lookup(identifier);
        if(!symbol.is_auxiliary)
          identifier_set.insert(identifier);
      }
    }

  std::vector<irep_idt> result;

  for(auto identifier : identifier_set)
    result.push_back(identifier);

  return result;
}

std::size_t
max_name_width(const std::vector<irep_idt> &identifiers, const namespacet &ns)
{
  std::size_t width = 0;

  for(auto identifier : identifiers)
  {
    auto &symbol = ns.lookup(identifier);
    width = std::max(symbol.display_name().size(), width);
  }

  return width;
}

std::vector<std::string> values(const trans_tracet &trace)
{
  return {};
}

void show_waveform(const trans_tracet &trace, const namespacet &ns)
{
  auto y_identifiers = lhs_symbols(trace, ns);

  // sort by display_name
  std::sort(
    y_identifiers.begin(),
    y_identifiers.end(),
    [&ns](const irep_idt &a, const irep_idt &b) {
      auto &a_symbol = ns.lookup(a);
      auto &b_symbol = ns.lookup(b);
      auto &a_name = a_symbol.display_name();
      auto &b_name = b_symbol.display_name();
      return a_name.compare(b_name) < 0;
    });

  std::map<std::pair<irep_idt, std::size_t>, std::string> value_map;
  std::map<std::size_t, std::size_t> column_width;

  for(std::size_t timeframe = 0; timeframe < trace.states.size(); timeframe++)
  {
    auto &state = trace.states[timeframe];
    for(auto &assignment : state.assignments)
    {
      auto &lhs = assignment.lhs;
      if(lhs.id() == ID_symbol)
      {
        auto identifier = to_symbol_expr(lhs).get_identifier();
        if(assignment.rhs.is_not_nil())
        {
          auto as_string = from_expr(ns, identifier, assignment.rhs);
          value_map[std::make_pair(identifier, timeframe)] = as_string;
          auto &width = column_width[timeframe];
          width = std::max(width, as_string.size());
          if(width < 2)
            width = 2;
        }
      }
    }
  }

  auto y_label_width = max_name_width(y_identifiers, ns);

  {
    consolet::out() << consolet::underline;
    consolet::out().width(y_label_width);
    consolet::out() << "";

    for(std::size_t x = 0; x < trace.states.size(); x++)
    {
      consolet::out() << ' ';
      if(consolet::is_terminal() && consolet::use_SGR())
        consolet::out() << ((x % 2) ? "\x1b[47m" : "");
      consolet::out().width(column_width[x]);
      consolet::out() << x % 100;
      if(consolet::is_terminal() && consolet::use_SGR())
        consolet::out() << "\x1b[49m";
    }

    consolet::out() << consolet::reset;
    consolet::out() << '\n';
  }

  for(auto y : y_identifiers)
  {
    auto &symbol = ns.lookup(y);

    if(consolet::is_terminal() && consolet::use_SGR())
      consolet::out() << "\x1b[97m\x1b[100m";
    consolet::out().width(y_label_width);
    consolet::out() << symbol.display_name();
    consolet::out() << consolet::reset;

    for(std::size_t x = 0; x < trace.states.size(); x++)
    {
      consolet::out() << ' ';
      if(consolet::is_terminal() && consolet::use_SGR())
        consolet::out() << ((x % 2) ? "\x1b[47m" : "");
      consolet::out().width(std::min(std::size_t(2), column_width[x]));
      consolet::out() << value_map[std::make_pair(y, x)];
      consolet::out() << consolet::reset;
    }

    consolet::out() << '\n';
  }
}
