/*******************************************************************\

Module: Predicate Abstraction Auxiliary Code

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PREDABS_AUX
#define CPROVER_PREDABS_AUX

#include <set>
#include <string>

#include <solvers/prop/prop_conv.h>

literalt make_pos(prop_convt &conv, const exprt &expr);

bool uses_symbol(const exprt &expr,
                 const std::set<irep_idt> &symbols);

#endif
