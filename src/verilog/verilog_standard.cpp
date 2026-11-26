/*******************************************************************\

Module: Verilog Standard

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_standard.h"

#include <util/invariant.h>

std::string as_string(verilog_standardt standard)
{
  switch(standard)
  {
  case verilog_standardt::NOT_SET:
    return "not set";
  case verilog_standardt::V1995:
    return "1364-1995";
  case verilog_standardt::V2001_NOCONFIG:
    return "1364-2001-noconfig";
  case verilog_standardt::V2001:
    return "1364-2001";
  case verilog_standardt::V2005:
    return "1364-2005";
  case verilog_standardt::V2005_VIS:
    return "1364-2005-vis";
  case verilog_standardt::V2005_SMV:
    return "1364-2005-smv";
  case verilog_standardt::SV2005:
    return "1800-2005";
  case verilog_standardt::SV2009:
    return "1800-2009";
  case verilog_standardt::SV2012:
    return "1800-2012";
  case verilog_standardt::SV2017:
    return "1800-2017";
  case verilog_standardt::SV2023:
    return "1800-2023";
  }

  UNREACHABLE;
}
