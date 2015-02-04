/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/*

  HW-CBMC
  Bounded Model Checking for ANSI-C
  Copyright (C) 2001-2004 Daniel Kroening <kroening@kroening.com>

*/

#include "hw_cbmc_parse_options.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char **argv)
{
  hw_cbmc_parse_optionst parse_options(argc, argv);
  return parse_options.main();
}
