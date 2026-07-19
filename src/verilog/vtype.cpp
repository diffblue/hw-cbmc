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
    vtype = UNSIGNED_BIT;
    width=to_unsignedbv_type(type).get_width();
  }
  else if(type.id()==ID_signedbv)
  {
    vtype = SIGNED_BIT;
    width=to_signedbv_type(type).get_width();
  }
  else if(type.id()==ID_bool)
  {
    width=1;
    vtype=BOOL;
  }
  else if(type.id()==ID_verilog_signedbv)
  {
    vtype = SIGNED_LOGIC;
    width=to_verilog_signedbv_type(type).get_width();
  }
  else if(type.id()==ID_verilog_unsignedbv)
  {
    vtype = UNSIGNED_LOGIC;
    width=to_verilog_unsignedbv_type(type).get_width();
  }
  else if(type.id() == ID_verilog_realtime || type.id() == ID_verilog_real)
  {
    vtype = REAL;
    width = 64;
  }
  else if(type.id() == ID_verilog_shortreal)
  {
    vtype = REAL;
    width = 32;
  }
  else if(type.id() == ID_verilog_chandle)
  {
    vtype = CHANDLE;
    width = 32;
  }
  else if(type.id() == ID_verilog_event)
  {
    vtype = EVENT;
    width = 32;
  }
  else if(type.id() == ID_verilog_string)
  {
    vtype = STRING;
    width = 0;
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

  case vtypet::UNSIGNED_BIT:
    return out << "unsigned-bit(" << vtype.get_width() << ")";

  case vtypet::SIGNED_BIT:
    return out << "signed-bit(" << vtype.get_width() << ")";

  case vtypet::SIGNED_LOGIC:
    return out << "signed-logic(" << vtype.get_width() << ")";

  case vtypet::UNSIGNED_LOGIC:
    return out << "unsigned-logic(" << vtype.get_width() << ")";

  case vtypet::BOOL:
    return out << "bool";

  case vtypet::REAL:
    return out << "real";

  case vtypet::NULL_TYPE:
    return out << "null";

  case vtypet::CHANDLE:
    return out << "chandle";

  case vtypet::EVENT:
    return out << "event";

  case vtypet::STRING:
    return out << "string";

  case vtypet::UNKNOWN:
  case vtypet::OTHER:
  default:
    return out << "?";
  }
}
