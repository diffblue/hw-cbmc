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

#include "ebmc_parse_options.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char **argv)
{
  ebmc_parse_optionst ebmc_parse_options(argc, argv);
  return ebmc_parse_options.main();
}
