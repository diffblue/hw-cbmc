/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/expr.h>

class namespacet;

std::string expr2smv(const exprt &, const namespacet &);
std::string type2smv(const typet &, const namespacet &);
