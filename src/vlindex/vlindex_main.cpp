/*******************************************************************\

Module: vlindex Main Module

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "vlindex_parse_options.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char **argv)
{
  vlindex_parse_optionst vlindex_parse_options(argc, argv);
  return vlindex_parse_options.main();
}
