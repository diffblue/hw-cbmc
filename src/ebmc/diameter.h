/*******************************************************************\

Module: Diameter Test

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DIAMETER_H
#define CPROVER_DIAMETER_H

#include <solvers/prop/prop.h>

literalt simple_diameter(propt &solver, const std::vector<bvt> &states);
literalt efficient_diameter(propt &solver, const std::vector<bvt> &states);

#endif
