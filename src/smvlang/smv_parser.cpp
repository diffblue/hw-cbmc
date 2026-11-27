/*******************************************************************\

Module: SMV Parse Tree

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smv_parser.h"

#define FLEX_PREFIX yysmv
#include <verilog/flex_interface.h>

smv_parsert *smv_parser_ptr = nullptr;

bool smv_parsert::parse()
{
  PRECONDITION(in != nullptr);

  // The scanner reads from 'in', and keeps track of line numbers.
  yysmvflext flex_scanner(*in);
  scanner = &flex_scanner;

  bool result;

  try
  {
    result = yysmvparse();
  }
  catch(...)
  {
    scanner = nullptr;
    throw;
  }

  scanner = nullptr;
  return result || scanner_error;
}

int smv_parsert::lex()
{
  PRECONDITION(scanner != nullptr);
  return scanner->lex();
}

const char *smv_parsert::token_text() const
{
  PRECONDITION(scanner != nullptr);
  return scanner->text();
}
