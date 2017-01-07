/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bv_varid.h"

/*******************************************************************\

Function: bv_varidt::as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string bv_varidt::as_string() const
{
  return id2string(id)+'['+std::to_string(bit_nr)+']';
}
