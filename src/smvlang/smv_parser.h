/*******************************************************************\

Module: SMV Parser

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SMV_PARSER_H
#define CPROVER_SMV_PARSER_H

#include <util/parser.h>

#include "smv_parse_tree.h"

int yysmvparse();

extern class smv_parsert *smv_parser_ptr;

class smv_parsert:public parsert
{
public:
  explicit smv_parsert(message_handlert &message_handler)
    : parsert(message_handler)
  {
    PRECONDITION(smv_parser_ptr == nullptr);
    smv_parser_ptr = this;
  }

  ~smv_parsert()
  {
    smv_parser_ptr = nullptr;
  }

  smv_parse_treet parse_tree;
  smv_parse_treet::modulet *module;
  
  virtual bool parse()
  {
    return yysmvparse();
  }
};

#endif
