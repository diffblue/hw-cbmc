/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/*

  EBMC
  Enhanced Bounded Model Checking
  Copyright (C) 2002 Daniel Kroening <kroening@handshake.de>

  Purpose: Main Module

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
  ebmc_parseoptionst ebmc_parseoptions(argc, argv);
  return ebmc_parseoptions.main();
}
