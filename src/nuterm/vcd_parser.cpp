/*******************************************************************\

Module: VCD Parser

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "vcd_parser.h"

#include <istream>

static bool is_whitespace(char ch)
{
  return ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n';
}

static std::string vcd_token(std::istream &in)
{
  std::string token;
  char ch;
  while(!in.eof())
  {
    ch = in.get();
    if(is_whitespace(ch))
    {
      if(!token.empty())
        return token;
    }
    else
      token += ch;
  }

  return token;
}

void vcd_command(vcdt &, const std::string &token, std::istream &in)
{
  // look for $end
  while(true)
  {
    auto t = vcd_token(in);
    if(t.empty() || t == "$end")
      return;
  }
}

vcdt vcd_parser(std::istream &in)
{
  vcdt vcd;

  while(true)
  {
    auto token = vcd_token(in);
    if(token.empty())
      break;
    switch(token[0])
    {
    case '$':
      vcd_command(vcd, token, in);
      break;
    case '#':
      // #decimal
      vcd.simulation_time(token.substr(1, std::string::npos));
      break;
    case '0':
    case '1':
    case 'x':
    case 'X':
    case 'z':
    case 'Z':
      // (0 | 1 | x | X | z | Z) identifier
      // one token, no space
      vcd.value_change(token.substr(0, 1), token.substr(1));
      break;
    case 'b':
    case 'B':
      // (b | B) value identifier
      // two tokens, space between value and identifier
      vcd.value_change(token.substr(1), vcd_token(in));
      break;
    case 'r':
    case 'R':
      // (r | R) value identifier
      // two tokens, space between value and identifier
      vcd.value_change(token.substr(1), vcd_token(in));
      break;
    default:
      break;
    }
  }

  return vcd;
}

std::ostream &operator << (std::ostream &out, const vcdt::statet &state)
{
  for(auto &[id, value] : state.changes)
    out << id << " = " << std::stoull(value, nullptr, 2) << '\n';
  return out;
}

std::vector<vcdt::statet> vcdt::full_trace() const
{
  std::vector<statet> result;
  result.reserve(states.size());

  for(auto &state : states)
  {
    if(result.empty())
    {
      // first state
      result.push_back(state);
    }
    else
    {
      statet full_state(state.simulation_time);

      // copy the previous map
      full_state.changes = result.back().changes;

      // apply the changes
      for(auto &change : state.changes)
        full_state.changes[change.first] = change.second;

      result.push_back(std::move(full_state));
    }
  }

  return result;
}
