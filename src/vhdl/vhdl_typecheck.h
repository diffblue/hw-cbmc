/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VHDL_TYPECHECK_H
#define CPROVER_VHDL_TYPECHECK_H

#include "context.h"

bool convert_vhdl(void *root, contextt &context, std::string &error);

#endif

