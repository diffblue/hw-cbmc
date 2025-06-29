/*******************************************************************\

Module: Property Instrumentation via Buechi Automata

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGIC_LTL_SVA_TO_STRING_H
#define CPROVER_TEMPORAL_LOGIC_LTL_SVA_TO_STRING_H

#include <util/numbering.h>
#include <util/std_expr.h>

class ltl_sva_to_string_unsupportedt
{
public:
  explicit ltl_sva_to_string_unsupportedt(exprt __expr)
    : expr(std::move(__expr))
  {
  }

  exprt expr;
};

/// create formula strings for external LTL to Buechi tools
class ltl_sva_to_stringt
{
public:
  // throws ltl_sva_to_string_unsupportedt when the conversion fails
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
    resultt(precedencet _p, std::string _s) : p(_p), s(std::move(_s))
    {
    }
    precedencet p;
    std::string s;
  };

  numberingt<exprt, irep_hash> atoms;

  using modet = enum { PROPERTY, SVA_SEQUENCE, BOOLEAN };

  resultt prefix(std::string s, const unary_exprt &, modet);
  resultt suffix(std::string s, const unary_exprt &, modet);
  resultt infix(std::string s, const exprt &, modet);
  resultt rec(const exprt &, modet);
};

#endif
