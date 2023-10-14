/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_parser.h"

#include <util/cout_message.h>
#include <util/unicode.h>

#include <fstream>
#include <iostream>
#include <stdio.h>

verilog_parsert verilog_parser;

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool parse_verilog_file(const std::string &filename)
{
  std::ifstream in(widen_if_needed(filename));
  console_message_handlert console_message_handler;

  verilog_parser.set_file(filename);
  verilog_parser.log.set_message_handler(console_message_handler);

  if(filename=="")
    verilog_parser.in=&std::cin;
  else
  {
    if(!in)
    {
      std::cerr << "failed to open " << filename << std::endl;
      return true;
    }

    verilog_parser.in=&in;
  }

  return verilog_parser.parse();
}
