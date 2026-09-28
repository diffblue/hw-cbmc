/*******************************************************************\

Module: vlsim Main Module

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "vlsim_parse_options.h"

int main(int argc, const char **argv)
{
  vlsim_parse_optionst vlsim_parse_options(argc, argv);
  return vlsim_parse_options.main();
}
