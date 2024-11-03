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
  std::string operator()(const exprt &expr)
  {
    return rec(expr, PROPERTY).s;
  }

  exprt atom(const std::string &) const;

protected:
  enum class precedencet
  {
    ATOM,
    PREFIX,
    SUFFIX,
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

  numberingt<exprt, irep_hash> atoms;

  using modet = enum { PROPERTY, SVA_SEQUENCE, BOOLEAN };

  resultt prefix(std::string s, const exprt &, modet);
  resultt suffix(std::string s, const exprt &, modet);
  resultt infix(std::string s, const exprt &, modet);
  resultt rec(const exprt &, modet);
};

#endif
