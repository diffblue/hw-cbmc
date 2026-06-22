/*******************************************************************\

Module: Main Module

Author: Kiro

\*******************************************************************/

#include "fastppa_parse_options.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char **argv)
{
  fastppa_parse_optionst parse_options(argc, argv);
  return parse_options.main();
}
