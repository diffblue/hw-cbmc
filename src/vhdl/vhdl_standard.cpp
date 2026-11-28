/*******************************************************************\

Module: VHDL Standard

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "vhdl_standard.h"

#include <util/invariant.h>

std::optional<vhdl_standardt> vhdl_standard_from_string(const std::string &src)
{
  if(src == "87")
    return vhdl_standardt::VHDL87;
  else if(src == "93")
    return vhdl_standardt::VHDL93;
  else if(src == "2008")
    return vhdl_standardt::VHDL2008;
  else
    return {};
}

std::string as_string(vhdl_standardt standard)
{
  switch(standard)
  {
  case vhdl_standardt::VHDL87:
    return "1076-1987";
  case vhdl_standardt::VHDL93:
    return "1076-1993";
  case vhdl_standardt::VHDL2008:
    return "1076-2008";
  }

  UNREACHABLE;
}
