/*******************************************************************\

Module: Verilog Standard

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_STANDARD_H
#define CPROVER_VERILOG_STANDARD_H

// This follows the version specifier in 1800-2017 Sec 22.14.
// "V2005_VIS" is an extension, meant to cover the variant of
// Verilog that the VIS model checker accepts.
// "V2005_SMV" is an extension, meant to cover the variant of
// Verilog that the Cadence SMV model checker accepts.
enum class verilog_standardt
{
  NOT_SET,
  V1995,
  V2001_NOCONFIG,
  V2001,
  V2005,
  V2005_VIS,
  V2005_SMV,
  SV2005,
  SV2009,
  SV2012,
  SV2017,
  SV2023
};

#endif // CPROVER_VERILOG_STANDARD_H
