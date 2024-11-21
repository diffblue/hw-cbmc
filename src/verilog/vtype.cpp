/*******************************************************************\

Module: Verilog Expression Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include <util/bitvector_types.h>
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
  if(type.id() == ID_integer)
  {
    vtype = INTEGER;
    width = 32;
  }
  else if(type.id() == ID_verilog_integer)
  {
    vtype=INTEGER;
    width = 32;
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
  else if(type.id() == ID_verilog_realtime || type.id() == ID_verilog_real)
  {
    vtype = VERILOG_REAL;
    width = 64;
  }
  else if(type.id() == ID_verilog_shortreal)
  {
    vtype = VERILOG_REAL;
    width = 32;
  }
  else if(type.id() == ID_verilog_chandle)
  {
    vtype = CHANDLE;
    width = 32;
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
  switch(vtype.vtype)
  {
  case vtypet::INTEGER:
    return out << "integer";
    
  case vtypet::UNSIGNED:
    return out << "unsigned(" << vtype.get_width() << ")";

  case vtypet::SIGNED:
    return out << "signed(" << vtype.get_width() << ")";
  
  case vtypet::VERILOG_SIGNED:
    return out << "verilog_signed(" << vtype.get_width() << ")";

  case vtypet::VERILOG_UNSIGNED:
    return out << "verilog_unsigned(" << vtype.get_width() << ")";

  case vtypet::BOOL:
    return out << "bool";

  case vtypet::VERILOG_REAL:
    return out << "real";

  case vtypet::CHANDLE:
    return out << "chandle";

  case vtypet::NULL_TYPE:
    return out << "null";

  case vtypet::UNKNOWN:
  case vtypet::OTHER:
  default:
    return out << "?";
  }
}

