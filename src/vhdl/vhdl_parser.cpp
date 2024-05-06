/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "vhdl_parser.h"

#include <util/cout_message.h>
#include <util/unicode.h>

#include <fstream>
#include <iostream>
#include <stdio.h>

vhdl_parsert *vhdl_parser_ptr = nullptr;
extern int yyvhdlparse();

/*******************************************************************\

Function: parse_vhdl_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool parse_vhdl_file(const std::string &filename)
{
  std::ifstream in(widen_if_needed(filename));
  console_message_handlert console_message_handler;

  vhdl_parsert vhdl_parser;
  vhdl_parser.set_file(filename);
  vhdl_parser.log.set_message_handler(console_message_handler);

  if(filename=="")
    vhdl_parser.in=&std::cin;
  else
  {
    if(!in)
    {
      std::cerr << "failed to open " << filename << std::endl;
      return true;
    }

    vhdl_parser.in=&in;
  }

  return vhdl_parser.parse();
}
