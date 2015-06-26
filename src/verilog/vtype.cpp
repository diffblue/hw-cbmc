/*******************************************************************\

Module: Verilog Expression Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include <util/std_types.h>

#include "verilog_types.h"
#include "vtype.h"

/*******************************************************************\

Function: vtypet::vtypet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

vtypet::vtypet(const typet &type)
{
  if(type.id()==ID_integer)
  {
    vtype=INTEGER;
    width=0;
  }
  else if(type.id()==ID_unsignedbv)
  {
    vtype=UNSIGNED;
    width=to_unsignedbv_type(type).get_width();
  }
  else if(type.id()==ID_signedbv)
  {
    vtype=SIGNED;
    width=to_signedbv_type(type).get_width();
  }
  else if(type.id()==ID_bool)
  {
    width=1;
    vtype=BOOL;
  }
  else if(type.id()==ID_verilog_signedbv)
  {
    vtype=VERILOG_SIGNED;
    width=to_verilog_signedbv_type(type).get_width();
  }
  else if(type.id()==ID_verilog_unsignedbv)
  {
    vtype=VERILOG_UNSIGNED;
    width=to_verilog_unsignedbv_type(type).get_width();
  }
  else 
  {
    width=0;
    vtype=OTHER;
  }
}

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &operator << (std::ostream &out, const vtypet &vtype)
{
  if(vtype.is_integer())
    return out << "integer";
  else if(vtype.is_unsigned())
    return out << "unsigned(" << vtype.get_width() << ")";
  else if(vtype.is_signed())
    return out << "signed(" << vtype.get_width() << ")";
  else if(vtype.is_verilog_signed())
    return out << "verilog_signed(" << vtype.get_width() << ")";
  else if(vtype.is_verilog_unsigned())
    return out << "verilog_unsigned(" << vtype.get_width() << ")";
  else if(vtype.is_bool())
    return out << "bool";
  else
    return out << "?";
}

