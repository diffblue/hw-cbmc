/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/*

  HW-CBMC
  Bounded Model Checking for ANSI-C
  Copyright (C) 2001-2004 Daniel Kroening <kroening@kroening.com>

*/

#include "parseoptions.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char **argv)
{
  hw_cbmc_parseoptionst parseoptions(argc, argv);
  return parseoptions.main();
}
