/*******************************************************************\

Module: Partial Canonicalization of a Predicate

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CANONICALIZE_H
#define CPROVER_CANONICALIZE_H

#include <util/expr.h>

void canonicalize(exprt &expr, bool &negation);
void canonicalize(exprt &expr);

#endif
