/*******************************************************************\

Module: Create abstract expression from concrete one

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ABSTRACT_EXPRESSION_H
#define CPROVER_ABSTRACT_EXPRESSION_H

#include "predicates.h"

void abstract_expression(const predicatest &predicates,
                       exprt &expr);

void abstract_expression(const predicatest &predicates,
                         exprt &expr, int choice);


#endif
