/*******************************************************************\

Module: Property Instrumentation via Buechi Automata

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGIC_LTL_SVA_TO_STRING_H
#define CPROVER_TEMPORAL_LOGIC_LTL_SVA_TO_STRING_H

#include <util/expr.h>
#include <util/numbering.h>

/// create formula strings for external LTL to Buechi tools
class ltl_sva_to_stringt
{
public:
  enum class precedencet
  {
    ATOM,
    PREFIX,
    INFIX
  };

  struct resultt
  {
    resultt(precedencet _p, std::string _s, exprt _e)
      : p(_p), s(std::move(_s)), e(std::move(_e))
    {
    }
    precedencet p;
    std::string s;
    exprt e;
  };

  resultt operator()(const exprt &expr)
  {
    return to_string_rec(expr);
  }

  numberingt<exprt, irep_hash> atoms;

protected:
  resultt prefix(std::string s, const exprt &);
  resultt infix(std::string s, const exprt &);
  resultt to_string_rec(const exprt &);
};

#endif
