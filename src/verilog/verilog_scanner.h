/*******************************************************************\

Module: Verilog Scanner

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_SCANNER_H
#define CPROVER_VERILOG_SCANNER_H

#include "verilog_standard.h"

/// the state of the Verilog scanner
class verilog_scannert
{
public:
  explicit verilog_scannert(verilog_standardt __standard) : standard(__standard)
  {
  }

  // to determine the set of keyworkds
  verilog_standardt standard;

  // for lexing strings
  std::string string_literal;
};

#endif
