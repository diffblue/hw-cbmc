/*******************************************************************\

Module: Properties and Initial preidcates for Predicate Abstraction

Author: Himanshu Jain

\*******************************************************************/

#ifndef CPROVER_VCEGAR_SPEC
#define CPROVER_VCEGAR_SPEC

#include <util/expr.h>

class specificationt
{
public:
  std::string property_string;
  exprt property;
  std::vector<exprt> preds_from_property;
};
  
#endif
